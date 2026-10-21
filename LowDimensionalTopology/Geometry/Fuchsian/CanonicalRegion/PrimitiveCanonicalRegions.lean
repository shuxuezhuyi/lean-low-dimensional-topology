/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalReconstruction
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianPrimitives
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import Mathlib.Algebra.Order.Group.Unbundled.Int
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal real translation lifts form a group homomorphism. -/
def hTranslationSLHom : Multiplicative ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℝ where
  toFun x:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL x.toAdd
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL]
  map_mul' x y := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.mul_apply,Fin.sum_univ_two,add_comm]

theorem hTranslationSL_zpow (t : ℝ) (n : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t^n=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((n : ℝ)*t) := by
  change hTranslationSLHom (Multiplicative.ofAdd t)^n= _
  rw [←map_zpow]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((Multiplicative.ofAdd t ^ n).toAdd)= _
  rw [toAdd_zpow]
  congr 1
  exact zsmul_eq_mul t n

/-- Exact inclusion for actual standard parabolic canonical regions. -/
theorem hCanonicalRegion_translation_subset_iff (s t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL s)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) ↔ |t|≤|s| := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_translation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_translation]
  constructor
  · intro h
    by_contra hnot
    have hst : |s| < |t| := lt_of_not_ge hnot
    have hsum : 0< |s|+|t| := by have hs:=abs_nonneg s;linarith
    let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 ((|s|+|t|)/4) (div_pos hsum (by norm_num))
    have hp : p∈{z : ℍ | |s|/2<z.im} := by change |s|/2<(|s|+|t|)/4;linarith
    have hh := h hp
    change |t|/2<(|s|+|t|)/4 at hh
    linarith
  · intro h z hz
    change |t|/2<z.im
    change |s|/2<z.im at hz
    linarith

/-- Every nonzero integer translation power has a canonical region contained in that of the generator. -/
theorem hCanonicalRegion_translation_zpow_subset (t : ℝ) (n : ℤ) (hn : n≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t^n)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
  rw [hTranslationSL_zpow,hCanonicalRegion_translation_subset_iff,abs_mul]
  have habs : (1:ℝ)≤|(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  nlinarith [abs_nonneg t]

/-- Maximality inside an infinite cyclic translation group is exactly primitivity up to inversion. -/
theorem hCanonicalRegion_maximal_translation_power_iff (t : ℝ) (ht : t≠0)
    (n : ℤ) (hn : n≠0) :
    (∀m : ℤ,m≠0 → _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t^m)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t^n)) ↔
      n=1 ∨ n= -1 := by
  constructor
  · intro h
    have hh := h 1 one_ne_zero
    rw [hTranslationSL_zpow,hTranslationSL_zpow,hCanonicalRegion_translation_subset_iff] at hh
    simp only [Int.cast_one,one_mul,abs_mul] at hh
    have habs : (1:ℝ)≤|(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have he : |(n : ℝ)|=1 := by nlinarith [abs_pos.mpr ht]
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp he with he | he
    · left
      exact_mod_cast he
    · right
      exact_mod_cast he
  · rintro (rfl | rfl)
    · intro m hm
      simpa only [zpow_one] using hCanonicalRegion_translation_zpow_subset t m hm
    · intro m hm
      simpa only [zpow_neg_one,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_inverse] using hCanonicalRegion_translation_zpow_subset t m hm

/-- The identity's strict canonical inequality gives the whole genuine plane. -/
theorem hCanonicalRegion_one : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)=univ := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_ne_zero _ (by norm_num [Matrix.trace_fin_two])]
  ext z
  simp

/-- The identity must be excluded from the source maximality comparison. -/
theorem hCanonicalRegion_identity_not_subset_translation :
    ¬_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) := by
  intro h
  let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (1/4) (by norm_num)
  have hp : p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by rw [hCanonicalRegion_one];trivial
  have hh := h hp
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_translation] at hh
  change |(1:ℝ)|/2<1/4 at hh
  norm_num at hh

/-- Simultaneous genuine conjugation preserves the actual inclusion relation. -/
theorem hCanonicalRegion_subset_conjugation_iff
    (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (q*A*q⁻¹)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (q*B*q⁻¹) ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation]
  exact Set.image_subset_image_iff (MulAction.toPerm q).injective

/-- The actual canonical region of every parabolic power is controlled by the absolute exponent. -/
theorem hCanonicalRegion_parabolic_zpow_subset_iff
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (m n : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (A^m)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (A^n) ↔ |(n:ℝ)|≤|(m:ℝ)| := by
  obtain ⟨q,t,ht,he⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rcases he with he | he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hpow (k : ℤ) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (q*A^k*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t^k) := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr
    rw [←conj_zpow,map_zpow,hproj,←map_zpow]
  rw [←hCanonicalRegion_subset_conjugation_iff _ _ q,hpow m,hpow n,
    hTranslationSL_zpow,hTranslationSL_zpow,hCanonicalRegion_translation_subset_iff,
    abs_mul,abs_mul]
  exact mul_le_mul_iff_left₀ (abs_pos.mpr ht)

/-- Every nontrivial parabolic integer power has a no-larger canonical region. -/
theorem hCanonicalRegion_parabolic_zpow_subset
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (n : ℤ) (hn : n≠0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (A^n)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A := by
  simpa only [zpow_one,Int.cast_one,abs_one] using
    (hCanonicalRegion_parabolic_zpow_subset_iff A hA n 1).mpr
      (by exact_mod_cast Int.one_le_abs hn)

/-- A point fixed by a genuine transformation is fixed by every integer power. -/
theorem primitive_mobius_zpow_fixed {f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {a :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (ha : f.val a=a) (n : ℤ) : (f^n).val a=a := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using _root_.LowDimensionalTopology.Geometry.Mobius.mobius_pow_fixed ha n
  | negSucc n =>
    simpa only [zpow_negSucc] using _root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_pow_fixed ha (n+1))

/-- A genuine root of a parabolic transformation is itself parabolic. -/
theorem mobius_parabolic_of_zpow {f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (n : ℤ)
    (h : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (f^n)) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f := by
  have hf : f≠1 := by intro he;apply h.1;rw [he,one_zpow]
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_fixedPoint_dichotomy f hf with hu | ⟨a,b,hab,hpair⟩
  · exact ⟨hf,hu⟩
  · obtain ⟨w,hw⟩ := h.2
    have ha := (hw a).mp (primitive_mobius_zpow_fixed ((hpair a).mpr (Or.inl rfl)) n)
    have hb := (hw b).mp (primitive_mobius_zpow_fixed ((hpair b).mpr (Or.inr rfl)) n)
    exact False.elim (hab (ha.trans hb.symm))

/-- Maximality compares every nonidentity element of each genuine fixed-point stabilizer. -/
def HasMaximalCanonicalRegion (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  ∀ p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p →
    ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H → (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p → _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1 →
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A

/-- A primitive parabolic has maximal actual canonical region in every fixed-point stabilizer. -/
theorem IsPrimitive.maximalCanonicalRegion_of_parabolic
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (A : Matrix.SpecialLinearGroup (Fin
      2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    HasMaximalCanonicalRegion H A := by
  intro p hAp B hB hBp hB0
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [hp.generates p hAp]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨hB,hBp⟩
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hn0 : n≠0 := by intro he;apply hB0;rw [he,zpow_zero] at hn;exact hn.symm
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr B (A^n) (by rw [map_zpow,hn])
  rw [he]
  exact hCanonicalRegion_parabolic_zpow_subset A hA n hn0

/-- Cyclic actual stabilizers and actual real lifts suffice for the reverse parabolic implication. -/
theorem primitive_parabolic_of_maximalCanonicalRegion
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hlift : ∀ f∈H,∃B : Matrix.SpecialLinearGroup (Fin 2)
      ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=f)
    (hcyclic : ∀p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsCyclic
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hmax : HasMaximalCanonicalRegion H A) :
    IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  apply primitive_iff_of_parabolic hA |>.mpr
  refine ⟨hmem,?_⟩
  intro p hp
  obtain ⟨f,hf⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p)).mp (hcyclic p)
  have hAf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈Subgroup.zpowers f := by
    rw [hf]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨hmem,hp⟩
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hAf
  have hn0 : n≠0 := by intro he;apply hA.1;rw [he,zpow_zero] at hn;exact hn.symm
  have hfP : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f := mobius_parabolic_of_zpow n (hn.symm ▸
    hA)
  have hfmem : f∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p := by
    rw [←hf]
    exact Subgroup.mem_zpowers f
  obtain ⟨hfH,hfp⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p
    f).mp hfmem
  obtain ⟨B,hB⟩ := hlift f hfH
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (B^n) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr A (B^n) (by rw [map_zpow,hB,hn])
  have hBA := hmax p hp B (hB ▸ hfH) (hB ▸ hfp) (hB ▸ hfP.1)
  rw [he] at hBA
  have hBP : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := hB ▸ hfP
  have hh : |(n:ℝ)|≤1 := by
    simpa only [zpow_one,Int.cast_one,abs_one] using
      (hCanonicalRegion_parabolic_zpow_subset_iff B hBP 1 n).mp (by simpa using hBA)
  have heq : |(n:ℝ)|=1 := le_antisymm hh (by exact_mod_cast Int.one_le_abs hn0)
  have hsign : n=1 ∨ n= -1 := by
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp heq with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rw [←hn]
  rcases hsign with rfl | rfl
  · simpa only [zpow_one] using hf
  · simpa only [zpow_neg_one,Subgroup.zpowers_inv] using hf

/-- The actual stabilizer of a conjugated point is the conjugate of its original stabilizer. -/
theorem primitive_boundaryStabilizer_conjugation (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val p)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p) := by
  ext f
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff]
  constructor
  · rintro ⟨hf,hfix⟩
    obtain ⟨g,hg,rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
      q H f).mp hf
    refine ⟨g,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mpr
      ⟨hg,?_⟩,rfl⟩
    apply q.val.injective
    change q•(g•p)=q•p
    change (q*g*q⁻¹)•(q•p)=q•p at hfix
    simpa only [mul_smul,inv_smul_smul] using hfix
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨hgH,hgp⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mp hg
    refine ⟨(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr
      ⟨g,hgH,rfl⟩,?_⟩
    change (q*g*q⁻¹)•(q•p)=q•p
    simp only [mul_smul,inv_smul_smul]
    exact congrArg q.val hgp

/-- Actual cyclic stabilizers survive the whole-group geometric normalization. -/
theorem FuchsianDisc.normalized_stabilizer_isCyclic
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup p) := by
  let q := D.halfPlaneNormalizer
  have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup p=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (q⁻¹.val p)) := by
    have h := primitive_boundaryStabilizer_conjugation H q (q⁻¹.val p)
    have hq : q.val (q⁻¹.val p)=p := by
      change q•(q⁻¹•p)=p
      exact smul_inv_smul q p
    rw [hq] at h
    exact h
  rw [he]
  let := D.stabilizer_isCyclic (q⁻¹.val p)
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (q⁻¹.val p))
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

/-- A normalized parabolic element is primitive exactly when its canonical region is maximal. -/
theorem FuchsianDisc.primitive_parabolic_iff_maximalCanonicalRegion
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup) :
    IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ↔ HasMaximalCanonicalRegion D.normalizedGroup A := by
  exact ⟨fun h=>h.maximalCanonicalRegion_of_parabolic A hA,
    primitive_parabolic_of_maximalCanonicalRegion D.normalizedGroup
      D.normalizedGroup_exists_realSL D.normalized_stabilizer_isCyclic A hA hmem⟩

/-- Logarithmic positive diagonal lifts retain the exact real additive parameter. -/
def hLogDilationSL (t : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨(!![Real.exp t,0;0,Real.exp (-t)] : Matrix (Fin 2) (Fin 2) ℝ),by
    rw [Matrix.det_fin_two]
    change Real.exp t*Real.exp (-t)-0*0=1
    rw [←Real.exp_add]
    simp⟩

/-- These actual positive diagonal matrices form a genuine one-parameter group. -/
def hLogDilationSLHom : Multiplicative ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℝ where
  toFun x:=hLogDilationSL x.toAdd
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hLogDilationSL]
  map_mul' x y := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hLogDilationSL,Matrix.mul_apply,Fin.sum_univ_two,Real.exp_add,mul_comm]

theorem hLogDilationSL_zpow (t : ℝ) (n : ℤ) :
    hLogDilationSL t^n=hLogDilationSL ((n:ℝ)*t) := by
  change hLogDilationSLHom (Multiplicative.ofAdd t)^n= _
  rw [←map_zpow]
  change hLogDilationSL ((Multiplicative.ofAdd t ^ n).toAdd)= _
  rw [toAdd_zpow]
  congr 1
  exact zsmul_eq_mul t n

/-- The literal canonical region of a logarithmic dilation is a strip with exact slope. -/
theorem hCanonicalRegion_logDilation (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (hLogDilationSL t)={z : ℍ | |Real.sinh t*z.re|<z.im} := by
  have ht : Matrix.trace (hLogDilationSL t).val≠0 := by
    rw [Matrix.trace_fin_two]
    change Real.exp t+Real.exp (-t)≠0
    positivity
  ext z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_mem_quadratic _ ht]
  have hq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic (hLogDilationSL t) z= -2*(Real.sinh t*z.re) := by
    change 0*(z.re^2+z.im^2)+(Real.exp (-t)-Real.exp t)*z.re-0= _
    rw [Real.sinh_eq]
    ring
  rw [hq,abs_mul]
  norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  change 2*|Real.sinh t*z.re|<2*z.im ↔ |Real.sinh t*z.re|<z.im
  constructor <;> intro h <;> linarith

/-- Exact inclusion of the genuine logarithmic-dilation regions. -/
theorem hCanonicalRegion_logDilation_subset_iff (s t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (hLogDilationSL s)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (hLogDilationSL t) ↔ |t|≤|s| := by
  rw [hCanonicalRegion_logDilation,hCanonicalRegion_logDilation]
  have hreduce : ({z : ℍ | |Real.sinh s*z.re|<z.im}⊆
      {z : ℍ | |Real.sinh t*z.re|<z.im}) ↔ |Real.sinh t|≤|Real.sinh s| := by
    constructor
    · intro h
      by_contra hn
      have hst : |Real.sinh s| < |Real.sinh t| := lt_of_not_ge hn
      have hy : 0<(|Real.sinh s|+|Real.sinh t|)/2 := by
        have hs:=abs_nonneg (Real.sinh s)
        linarith
      let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 1 ((|Real.sinh s|+|Real.sinh t|)/2) hy
      have hzs : z∈{z : ℍ | |Real.sinh s*z.re|<z.im} := by
        change |Real.sinh s*1|<(|Real.sinh s|+|Real.sinh t|)/2
        rw [mul_one]
        linarith
      have hzt := h hzs
      change |Real.sinh t*1|<(|Real.sinh s|+|Real.sinh t|)/2 at hzt
      rw [mul_one] at hzt
      linarith
    · intro h z hz
      change |Real.sinh t*z.re|<z.im
      change |Real.sinh s*z.re|<z.im at hz
      rw [abs_mul] at hz ⊢
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h (abs_nonneg _)) hz
  rw [hreduce,Real.abs_sinh,Real.abs_sinh,Real.sinh_le_sinh]

/-- Logarithmic diagonal matrices act by the actual positive Euclidean dilation. -/
theorem hLogDilationSL_coe (t : ℝ) (z : ℍ) :
    ((hLogDilationSL t•z : ℍ) : ℂ)=(Real.exp (2*t):ℂ)*z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change ((Real.exp t:ℂ)*z+0)/(0*z+(Real.exp (-t):ℂ))= _
  have he : Real.exp (2*t)=Real.exp t*Real.exp t := by rw [←Real.exp_add];congr 1;ring
  rw [Real.exp_neg,he]
  push_cast
  simp only [add_zero,zero_mul,zero_add,div_inv_eq_mul]
  ring

/-- The whole genuine logarithmic-dilation map equals the usual positive diagonal lift. -/
theorem realSLMobius_logDilation (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (Real.exp (2*t)) (Real.exp_pos _)) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_of_native_action
  intro z
  apply UpperHalfPlane.ext
  rw [hLogDilationSL_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe]

/-- Every actual hyperbolic real Mobius map admits a nonzero logarithmic diagonal parameter. -/
theorem realSLMobius_hyperbolic_log_normal_form
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,∃t : ℝ,t≠0 ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t) := by
  have ht := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA
  obtain ⟨q,k,hk,hk1,_,ha⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_normalizer A hA.1.1 ht
  let t:=Real.log k/2
  have he : Real.exp (2*t)=k := by dsimp [t];rw [show 2*(Real.log k/2)=Real.log k by ring,Real.exp_log hk]
  refine ⟨q,t,?_,?_⟩
  · intro ht0
    apply hk1
    rw [ht0] at he
    simpa only [mul_zero,Real.exp_zero] using he.symm
  · rw [realSLMobius_logDilation]
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_of_native_action
    intro z
    apply UpperHalfPlane.ext
    rw [ha,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,he]

/-- Exact exponent control of inclusion for every actual hyperbolic transformation. -/
theorem hCanonicalRegion_hyperbolic_zpow_subset_iff
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (m n : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (A^m)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (A^n) ↔ |(n:ℝ)|≤|(m:ℝ)| := by
  obtain ⟨q,t,ht,hproj⟩ := realSLMobius_hyperbolic_log_normal_form A hA
  have hpow (k : ℤ) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (q*A^k*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (hLogDilationSL t^k) := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr
    rw [←conj_zpow,map_zpow,hproj,←map_zpow]
  rw [←hCanonicalRegion_subset_conjugation_iff _ _ q,hpow m,hpow n,
    hLogDilationSL_zpow,hLogDilationSL_zpow,hCanonicalRegion_logDilation_subset_iff,
    abs_mul,abs_mul]
  exact mul_le_mul_iff_left₀ (abs_pos.mpr ht)

/-- Primitive hyperbolics dominate all nontrivial integer powers of their genuine generators. -/
theorem hCanonicalRegion_hyperbolic_zpow_subset
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (n : ℤ) (hn : n≠0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (A^n)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A := by
  simpa only [zpow_one,Int.cast_one,abs_one] using
    (hCanonicalRegion_hyperbolic_zpow_subset_iff A hA n 1).mpr
      (by exact_mod_cast Int.one_le_abs hn)

/-- A nonidentity integer power has exactly the same actual boundary fixed set as its base. -/
theorem mobius_nontrivial_zpow_sameFixedPoints (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (n
  : ℤ)
    (hn : f^n≠1) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints f (f^n) := by
  have hf : f≠1 := by intro he;apply hn;rw [he,one_zpow]
  have hc : Commute f (f^n) := Commute.self_zpow f n
  rcases (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_commute_iff_preserves_fixed_points_and_configuration f
    (f^n) hf hn).2.mp hc with hs | ⟨_,_,_,_,hd⟩
  · exact hs
  · obtain ⟨w,hw⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_has_boundary_fixed f hf
    exact False.elim (Set.disjoint_left.mp hd hw (primitive_mobius_zpow_fixed hw n))

/-- A real lift whose nonidentity integer power is hyperbolic is itself genuinely hyperbolic. -/
theorem realSLMobius_hyperbolic_of_zpow
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (n : ℤ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B^n))) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
  have hn : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)^n≠1 := by simpa only [map_zpow] using hA.1.1
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1 := by intro he;apply hn;rw [he,one_zpow]
  have hs := mobius_nontrivial_zpow_sameFixedPoints (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    B) n hn
  have htA := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff (B^n) hA.1.1).mp hA
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hf).mpr
  by_contra hnot
  have hle := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with he | hp
  · let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B he
    have hzB : B•z=z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B he z).mpr rfl
    have hzM : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hzB]
    have hzA := primitive_mobius_zpow_fixed hzM n
    rw [←map_zpow] at hzA
    have hz0 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_fixed_im (B^n) htA (z:ℂ) hzA
    exact z.im_ne_zero hz0
  · have hP := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff B hf).mpr hp
    obtain ⟨w,hw⟩ := hP.2
    apply hA.1.not_parabolic
    refine ⟨hA.1.1,w,?_⟩
    intro p
    rw [map_zpow]
    exact (hs p).symm.trans (hw p)

/-- A primitive hyperbolic has maximal actual canonical region in its fixed-point stabilizers. -/
theorem IsPrimitive.maximalCanonicalRegion_of_hyperbolic
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (A : Matrix.SpecialLinearGroup (Fin
      2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    HasMaximalCanonicalRegion H A := by
  intro p hAp B hB hBp hB0
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [hp.generates p hAp]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨hB,hBp⟩
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hn0 : n≠0 := by intro he;apply hB0;rw [he,zpow_zero] at hn;exact hn.symm
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr B (A^n) (by rw [map_zpow,hn])
  rw [he]
  exact hCanonicalRegion_hyperbolic_zpow_subset A hA n hn0

/-- The exact reverse hyperbolic implication uses only actual lifts and genuine cyclic stabilizers. -/
theorem primitive_hyperbolic_of_maximalCanonicalRegion
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hlift : ∀ f∈H,∃B : Matrix.SpecialLinearGroup (Fin 2)
      ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=f)
    (hcyclic : ∀p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsCyclic
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hmax : HasMaximalCanonicalRegion H A) :
    IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
  apply primitive_iff_of_hyperbolic hA |>.mpr
  refine ⟨hmem,?_⟩
  intro p hp
  obtain ⟨f,hf⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p)).mp (hcyclic p)
  have hAf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈Subgroup.zpowers f := by
    rw [hf]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨hmem,hp⟩
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hAf
  have hn0 : n≠0 := by intro he;apply hA.1.1;rw [he,zpow_zero] at hn;exact hn.symm
  have hfmem : f∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p := by
    rw [←hf]
    exact Subgroup.mem_zpowers f
  obtain ⟨hfH,hfp⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p
    f).mp hfmem
  obtain ⟨B,hB⟩ := hlift f hfH
  have hBA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B^n)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A := by rw [map_zpow,hB,hn]
  have hBP : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) :=
    realSLMobius_hyperbolic_of_zpow B n (hBA ▸ hA)
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (B^n) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_congr A (B^n) hBA.symm
  have hsub := hmax p hp B (hB ▸ hfH) (hB ▸ hfp) hBP.1.1
  rw [he] at hsub
  have hh : |(n:ℝ)|≤1 := by
    simpa only [zpow_one,Int.cast_one,abs_one] using
      (hCanonicalRegion_hyperbolic_zpow_subset_iff B hBP 1 n).mp (by simpa using hsub)
  have heq : |(n:ℝ)|=1 := le_antisymm hh (by exact_mod_cast Int.one_le_abs hn0)
  have hsign : n=1 ∨ n= -1 := by
    rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp heq with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rw [←hn]
  rcases hsign with rfl | rfl
  · simpa only [zpow_one] using hf
  · simpa only [zpow_neg_one,Subgroup.zpowers_inv] using hf

/-- A normalized hyperbolic element is primitive exactly when its canonical region is maximal. -/
theorem FuchsianDisc.primitive_hyperbolic_iff_maximalCanonicalRegion
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup) :
    IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ↔ HasMaximalCanonicalRegion D.normalizedGroup A := by
  exact ⟨fun h=>h.maximalCanonicalRegion_of_hyperbolic A hA,
    primitive_hyperbolic_of_maximalCanonicalRegion D.normalizedGroup
      D.normalizedGroup_exists_realSL D.normalized_stabilizer_isCyclic A hA hmem⟩

end LowDimensionalTopology.Geometry.Fuchsian
