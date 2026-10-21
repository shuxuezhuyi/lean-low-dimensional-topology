module
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.FiniteIndexConjugacy
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.MobiusEndpointDensity
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.HyperbolicProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.Pointwise
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A cyclic actual Mobius subgroup fixes every fixed point of any nonidentity member. -/
theorem cyclic_mobius_fixedPoint (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hK :
  IsCyclic K)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfK : f ∈ K) (hf : f ≠ 1)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p = p) : ∀ g ∈ K, g.val p = p := by
  have := hK
  obtain ⟨a, ha⟩ := exists_zpow_surjective K
  obtain ⟨n, hn⟩ := ha ⟨f, hfK⟩
  have hnf : a.val ^ n = f := congrArg (fun k : K => k.val) hn
  have han : a.val ≠ 1 := by intro h; simp only [h, one_zpow] at hnf; exact hf hnf.symm
  have hnp : a.val ^ n ≠ 1 := hnf ▸ hf
  have hs := mobius_zpow_same_fixedPoints a.val han n hnp
  have hap : a.val.val p = p := (hs p).mpr (hnf.symm ▸ hfp)
  intro g hg
  obtain ⟨m, hm⟩ := ha ⟨g, hg⟩
  have hmg : a.val ^ m = g := congrArg (fun k : K => k.val) hm
  rw [← hmg]
  exact mobius_zpow_fixed hap m

/-- Every genuine fixed-point stabilizer containing a nonidentity element is maximal cyclic. -/
theorem nonidentity_stabilizer_isMaximalCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f ∈ H) (hf : f ≠
      1)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p = p) :
    IsMaximalCyclicIn H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p) := by
  refine ⟨fun g hg => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mp
    hg).1,
    D.stabilizer_isCyclic p, ?_⟩
  intro L hLH hL hKL
  apply le_antisymm _ hKL
  intro g hg
  refine (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p g).mpr ⟨hLH hg, ?_⟩
  exact cyclic_mobius_fixedPoint L hL f
    (hKL ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p f).mpr ⟨hfH,
      hfp⟩)) hf p hfp g hg

def fuchsianMaximalHyperbolicCyclicSubgroups (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    Set (Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
  {K | IsMaximalCyclicIn H K ∧ ∃ f ∈ K, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f}

/-- Every original hyperbolic element lies in an actual maximal hyperbolic cyclic subgroup. -/
theorem hyperbolic_mem_maximal_cyclic {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f ∈ H) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) :
    ∃ K ∈ fuchsianMaximalHyperbolicCyclicSubgroups H, f ∈ K := by
  obtain ⟨p, hp⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_has_boundary_fixed f hf.1.1
  have hmem := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p f).mpr ⟨hfH, hp⟩
  refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p, ?_, hmem⟩
  exact ⟨nonidentity_stabilizer_isMaximalCyclic D f hfH hf.1.1 p hp, f, hmem, hf⟩

/-- A literal cyclic Mobius subgroup has an actual generator, not an assumed generator field. -/
theorem cyclic_mobius_exists_generator (K : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hK : IsCyclic K) :
    ∃ a ∈ K, Subgroup.zpowers a = K := by
  have := hK
  obtain ⟨a, ha⟩ := exists_zpow_surjective K
  refine ⟨a.val, a.property, ?_⟩
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr a.property
  · intro g hg
    obtain ⟨n, hn⟩ := ha ⟨g, hg⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg (fun k : K => k.val) hn⟩

/-- Generators of an actual hyperbolic cyclic subgroup are themselves hyperbolic. -/
theorem hyperbolic_cyclic_generator {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H) (hK : IsCyclic K)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfK : f ∈ K) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) :
    ∃ a ∈ H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic a ∧ Subgroup.zpowers a = K := by
  obtain ⟨a, haK, haGen⟩ := cyclic_mobius_exists_generator K hK
  have hfPow : f ∈ Subgroup.zpowers a := haGen.symm ▸ hfK
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hfPow
  have han : a ≠ 1 := by intro he; simp only [he, one_zpow] at hn; exact hf.1.1 hn.symm
  have hnp : a ^ n ≠ 1 := hn ▸ hf.1.1
  have hs := mobius_zpow_same_fixedPoints a han n hnp
  have hsame : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints a f := hn ▸ hs
  obtain ⟨p, q, hpq,
    hfix⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_loxodromic_boundary_fixed_pair f hf.1
  have hfp := (hfix p).mpr (Or.inl rfl)
  have hfq := (hfix q).mpr (Or.inr rfl)
  have hap := (hsame p).mpr hfp
  have haq := (hsame q).mpr hfq
  refine ⟨a, hKH haK, ?_, haGen⟩
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy a han with hP | hL | hE
  · obtain ⟨w, hw⟩ := hP.2
    exact False.elim (hpq (((hw p).mp hap).trans ((hw q).mp haq).symm))
  · exact D.loxodromic_hyperbolic ⟨a, hKH haK⟩ hL
  · have hpf := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier f hf D.isDisc
      (D.image_eq ⟨f, hKH hfK⟩) hfp
    exact False.elim ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier a hE
      D.isDisc
      (D.image_eq ⟨a, hKH haK⟩) hap) hpf)

/-- The literal conjugation action on actual Mobius subgroups. -/
@[instance_reducible]
def mobiusSubgroupConjugationAction (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    MulAction H (Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
  MulAction.compHom _ (ConjAct.toConjAct.toMonoidHom.comp H.subtype)

def fuchsianHyperbolicCyclicConjugacySetoid (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    Setoid (fuchsianMaximalHyperbolicCyclicSubgroups H) :=
  let _ := mobiusSubgroupConjugationAction H
  Setoid.comap Subtype.val (MulAction.orbitRel H (Subgroup
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))

def FuchsianHyperbolicCyclicConjugacyClasses (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
  Quotient (fuchsianHyperbolicCyclicConjugacySetoid H)

theorem fuchsianHyperbolicCyclicConjugacySetoid_iff (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (K L : fuchsianMaximalHyperbolicCyclicSubgroups H) :
    (fuchsianHyperbolicCyclicConjugacySetoid H).r K L ↔
      ∃ g : H, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g.val L.val = K.val := by
  let _ := mobiusSubgroupConjugationAction H
  change MulAction.orbitRel H (Subgroup
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) K.val L.val ↔ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  rfl

/-- Each literal maximal-hyperbolic conjugacy class has a genuine hyperbolic generator. -/
theorem fuchsianHyperbolicClass_exists_generator {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (ω : FuchsianHyperbolicCyclicConjugacyClasses H) :
    ∃ a : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic a.val ∧ Subgroup.zpowers a.val = ω.out.val := by
  obtain ⟨hK, f, hfK, hf⟩ := ω.out.property
  obtain ⟨a, haH, haHyp, hgen⟩ := hyperbolic_cyclic_generator D ω.out.val hK.1 hK.2.1 f hfK hf
  exact ⟨⟨a, haH⟩, haHyp, hgen⟩

def fuchsianHyperbolicClassGenerator {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H)
    (ω : FuchsianHyperbolicCyclicConjugacyClasses H) : H :=
  Classical.choose (fuchsianHyperbolicClass_exists_generator D ω)

theorem fuchsianHyperbolicClassGenerator_spec {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (ω : FuchsianHyperbolicCyclicConjugacyClasses H) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianHyperbolicClassGenerator D ω).val ∧
      Subgroup.zpowers (fuchsianHyperbolicClassGenerator D ω).val = ω.out.val :=
  Classical.choose_spec (fuchsianHyperbolicClass_exists_generator D ω)

/-- Every actual hyperbolic is a conjugate of a power of an actual class generator. -/
theorem hyperbolic_conjugate_class_generator_zpow {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) :
    ∃ (ω : FuchsianHyperbolicCyclicConjugacyClasses H) (g : H) (n : ℤ),
      f = g * (fuchsianHyperbolicClassGenerator D ω) ^ n * g⁻¹ := by
  obtain ⟨K, hK, hfK⟩ := hyperbolic_mem_maximal_cyclic D f.val f.property hf
  let ω : FuchsianHyperbolicCyclicConjugacyClasses H :=
    Quotient.mk (fuchsianHyperbolicCyclicConjugacySetoid H) ⟨K, hK⟩
  have hrel : (fuchsianHyperbolicCyclicConjugacySetoid H).r ⟨K, hK⟩ ω.out :=
    Quotient.exact (Quotient.out_eq' ω).symm
  obtain ⟨g, hg⟩ := (fuchsianHyperbolicCyclicConjugacySetoid_iff H ⟨K, hK⟩ ω.out).mp hrel
  have hmem : f.val ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g.val ω.out.val := hg.symm ▸ hfK
  obtain ⟨a, ha, hea⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    g.val ω.out.val f.val).mp hmem
  rw [← (fuchsianHyperbolicClassGenerator_spec D ω).2] at ha
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
  refine ⟨ω, g, n, ?_⟩
  apply Subtype.ext
  change f.val = g.val * (fuchsianHyperbolicClassGenerator D ω).val ^ n * g.val⁻¹
  rw [hn]
  exact hea.symm

/-- Finite maximal hyperbolic classes would give bounded trace replacements on every actual axis. -/
theorem finite_hyperbolic_classes_bounded_trace_same_fixedPoints
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    [Finite (FuchsianHyperbolicCyclicConjugacyClasses H)] :
    ∃ B : ℝ, ∀ f : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val →
      ∃ q : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic q.val ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints q.val f.val ∧
        ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace q.val‖ ≤ B := by
  have hfin : (range (fun ω : FuchsianHyperbolicCyclicConjugacyClasses H =>
      ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (fuchsianHyperbolicClassGenerator D
        ω).val‖)).Finite := finite_range _
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B, ?_⟩
  intro f hf
  obtain ⟨ω, g, n, he⟩ := hyperbolic_conjugate_class_generator_zpow D f hf
  let q : H := g * fuchsianHyperbolicClassGenerator D ω * g⁻¹
  have hq : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic q.val := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ _
    (fuchsianHyperbolicClassGenerator_spec D ω).1
  have hpow : q.val ^ n = f.val := by
    change (g.val * (fuchsianHyperbolicClassGenerator D ω).val * g.val⁻¹) ^ n = f.val
    rw [conj_zpow]
    exact congrArg Subtype.val he.symm
  refine ⟨q, hq, hpow ▸ mobius_zpow_same_fixedPoints q.val hq.1.1 n (hpow ▸ hf.1.1), ?_⟩
  change ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (g.val * (fuchsianHyperbolicClassGenerator D
    ω).val * g.val⁻¹)‖ ≤ B
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation]
  exact hB ⟨ω, rfl⟩

/-- The genuine bounded-trace replacement property transports to the actual conjugate subgroup. -/
theorem bounded_trace_same_fixedPoints_conjugation (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (B : ℝ)
    (hB : ∀ f : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val →
      ∃ r : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic r.val ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints r.val f.val ∧
        ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace r.val‖ ≤ B) :
    ∀ f : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val →
      ∃ r : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,
        _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic r.val ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints r.val f.val ∧
          ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace r.val‖ ≤ B := by
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have he (a : H) : (e a).val = q * a.val * q⁻¹ := rfl
  intro f hf
  have hfo : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (e.symm f).val := by
    apply (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation _ q).mp
    rw [← he, e.apply_symm_apply]
    exact hf
  obtain ⟨r, hr, hs, hb⟩ := hB (e.symm f) hfo
  refine ⟨e r, ?_, ?_, ?_⟩
  · rw [he]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ q hr
  · have ht := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSameFixedPoints_conjugation r.val (e.symm f).val
    q).mpr hs
    rwa [← he, ← he, e.apply_symm_apply] at ht
  · rw [he, _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation]
    exact hb

/-- Every limit neighborhood contains infinitely many actual limit points. -/
theorem mobiusLimitSet_open_inter_infinite (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (U : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hU : IsOpen U)
    (hne : (U ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H).Nonempty) : (U ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H).Infinite := by
  obtain ⟨p, hp⟩ := hne
  exact Set.Infinite.of_accPt (((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_perfect H
    hH).acc.open_inter hU) p hp)

/-- The actual real fixed-point equations control all coefficients and their discriminant. -/
theorem hSL_fixed_pair_coefficients (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (u v : ℝ) (huv : u ≠ v)
    (hu : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (u : ℂ))
    (hv : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((v : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (v : ℂ)) :
    A 1 0 * (u + v) = A 0 0 - A 1 1 ∧
      A 0 1 = -A 1 0 * u * v ∧
      A 1 0 ^ 2 * (u - v) ^ 2 = (Matrix.trace A.val) ^ 2 - 4 := by
  have hpu := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fixed_real_polynomial A u hu
  have hpv := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fixed_real_polynomial A v hv
  have he : (u - v) * (A 1 0 * (u + v) + A 1 1 - A 0 0) = 0 := by nlinarith
  have hlin : A 1 0 * (u + v) = A 0 0 - A 1 1 := by
    have h := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr huv)
    linarith
  have hb : A 0 1 = -A 1 0 * u * v := by
    have h := congrArg (fun x : ℝ => x * u) hlin
    nlinarith
  have hdet := A.property
  rw [Matrix.det_fin_two] at hdet
  refine ⟨hlin, hb, ?_⟩
  calc
    A 1 0 ^ 2 * (u - v) ^ 2 = (A 1 0 * (u + v)) ^ 2 + 4 * A 0 1 * A 1 0 := by rw [hb]; ring
    _ = (A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0 := by rw [hlin]
    _ = (Matrix.trace A.val) ^ 2 - 4 := by rw [Matrix.trace_fin_two]; nlinarith

/-- The genuine projective norm of a real determinant-one matrix is its real Frobenius norm. -/
theorem realSLMobius_normalizedNorm_sq (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ^ 2 =
      A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply,
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm_specialLinearProjection,
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_sq]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Uniform trace and separated bounded ideal endpoints give a genuine uniform matrix-norm bound. -/
theorem hSL_bounded_fixed_pair_norm_bound (R δ B : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (u v : ℝ),
      |u| ≤ R → |v| ≤ R → δ ≤ |u - v| →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((u : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (u : ℂ) →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((v : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (v : ℂ) →
      (Matrix.trace A.val) ^ 2 ≤ B → _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ≤ M := by
  let C := Real.sqrt B / δ
  have hC : 0 ≤ C := div_nonneg (Real.sqrt_nonneg _) hδ.le
  let S := Real.sqrt B + C * (2 * R) + C * R ^ 2 + C + 1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨2 * S, by positivity, ?_⟩
  intro A u v huR hvR hsep hu hv ht
  have huv : u ≠ v := by intro h; simp only [h, sub_self, abs_zero] at hsep; linarith
  obtain ⟨hlin, hb, hdisc⟩ := hSL_fixed_pair_coefficients A u v huv hu hv
  have hprod : |A 1 0| * |u - v| ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, sq_abs, sq_abs, Real.sq_sqrt hB, hdisc]
    linarith
  have hc : |A 1 0| ≤ C := by
    apply (le_div_iff₀ hδ).mpr
    exact (mul_le_mul_of_nonneg_left hsep (abs_nonneg _)).trans hprod
  have htrace : |A 0 0 + A 1 1| ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hB]
    simpa only [Matrix.trace_fin_two] using ht
  have hdiff : |A 0 0 - A 1 1| ≤ C * (2 * R) := by
    calc
      |A 0 0 - A 1 1| = |A 1 0| * |u + v| := by rw [← hlin, abs_mul]
      _ ≤ C * (|u| + |v|) := mul_le_mul hc (abs_add_le u v) (abs_nonneg _) hC
      _ ≤ C * (2 * R) := mul_le_mul_of_nonneg_left (by linarith) hC
  have huvR : |u| * |v| ≤ R ^ 2 := by
    simpa only [pow_two] using mul_le_mul huR hvR (abs_nonneg v) hR
  have hbnd : |A 0 1| ≤ C * R ^ 2 := by
    calc
      |A 0 1| = |A 1 0| * (|u| * |v|) := by rw [hb]; simp only [abs_mul, abs_neg]; ring
      _ ≤ C * R ^ 2 := mul_le_mul hc huvR (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC
  have ha2 : 2 * |A 0 0| ≤ Real.sqrt B + C * (2 * R) := by
    calc
      2 * |A 0 0| = |(A 0 0 + A 1 1) + (A 0 0 - A 1 1)| := by
        rw [show (A 0 0 + A 1 1) + (A 0 0 - A 1 1) = 2 * A 0 0 by ring, abs_mul]
        norm_num
      _ ≤ |A 0 0 + A 1 1| + |A 0 0 - A 1 1| := abs_add_le _ _
      _ ≤ _ := add_le_add htrace hdiff
  have hd2 : 2 * |A 1 1| ≤ Real.sqrt B + C * (2 * R) := by
    calc
      2 * |A 1 1| = |(A 0 0 + A 1 1) - (A 0 0 - A 1 1)| := by
        rw [show (A 0 0 + A 1 1) - (A 0 0 - A 1 1) = 2 * A 1 1 by ring, abs_mul]
        norm_num
      _ ≤ |A 0 0 + A 1 1| + |A 0 0 - A 1 1| := abs_sub _ _
      _ ≤ _ := add_le_add htrace hdiff
  have hcR : 0 ≤ C * (2 * R) := by positivity
  have hcR2 : 0 ≤ C * R ^ 2 := by positivity
  have haS : |A 0 0| ≤ S := by dsimp [S]; nlinarith [Real.sqrt_nonneg B]
  have hbS : |A 0 1| ≤ S := by dsimp [S]; linarith [Real.sqrt_nonneg B]
  have hcS : |A 1 0| ≤ S := by dsimp [S]; linarith [Real.sqrt_nonneg B]
  have hdS : |A 1 1| ≤ S := by dsimp [S]; nlinarith [Real.sqrt_nonneg B]
  have hsq (x : ℝ) (hx : |x| ≤ S) : x ^ 2 ≤ S ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hS).mpr hx
  have hn : 0 ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius, MonoidHom.comp_apply,
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm_specialLinearProjection]
    exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_nonneg _
  apply (sq_le_sq₀ hn (by positivity : 0 ≤ 2 * S)).mp
  rw [realSLMobius_normalizedNorm_sq]
  nlinarith [hsq _ haS, hsq _ hbS, hsq _ hcS, hsq _ hdS]

/-- In a genuine discrete real subgroup, bounded separated fixed endpoints and trace give finitely many maps. -/
theorem discrete_realSL_bounded_fixed_pair_trace_finite
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hH :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hreal : ∀ f ∈ H, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = f)
    (R δ B : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) (hB : 0 ≤ B) :
    {f : H | ∃ u v : ℝ, |u| ≤ R ∧ |v| ≤ R ∧ δ ≤ |u - v| ∧
      f.val.val ((u : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (u : ℂ) ∧
      f.val.val ((v : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (v : ℂ) ∧
      ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace f.val‖ ≤ B}.Finite := by
  obtain ⟨M, _hM, hbound⟩ := hSL_bounded_fixed_pair_norm_bound R δ B hR hδ hB
  apply (_root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_norm_sublevel_finite H hH M).subset
  rintro f ⟨u, v, huR, hvR, hsep, huf, hvf, ht⟩
  obtain ⟨A, hA⟩ := hreal f.val f.property
  have htr : (Matrix.trace A.val) ^ 2 ≤ B := by
    rw [← hA, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at ht
    exact ht
  have hm := hbound A u v huR hvR hsep (by rwa [hA]) (by rwa [hA]) htr
  rwa [hA] at hm

/-- Every actual real projective hyperbolic action is hyperbolic on the genuine half-plane. -/
theorem realSL_loxodromic_hyperbolic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) :=
  ⟨hA, _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc,
    realSLMobius_image_openHalfPlane A⟩

/-- A real subgroup's genuine limit set lies on the actual compactified real line. -/
theorem realSL_limitSet_subset_halfPlaneIdealBoundary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hreal : ∀ f ∈ H, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = f) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H ⊆ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary := by
  apply closure_minimal _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.isCompact_halfPlaneIdealBoundary.isClosed
  rintro p ⟨f, hf, hfp⟩
  obtain ⟨A, hA⟩ := hreal f.val f.property
  have hL : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := hA.symm ▸ hf
  have ht := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A
    hL.1).mp (realSL_loxodromic_hyperbolic A hL)
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_fixed_boundary A ht p (hA.symm ▸ hfp)

/-- A non-elementary real subgroup has two distinct finite real limit points. -/
theorem realSL_limitSet_exists_real_pair (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hH :
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    (hreal : ∀ f ∈ H, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = f) :
    ∃ u v : ℝ, u ≠ v ∧ ((u : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H ∧
      ((v : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H := by
  have hinf : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H).Infinite :=
    fun hfin => _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_not_countable H hH hfin.countable
  obtain ⟨p, hp⟩ := (hinf.sdiff (finite_singleton (∞ :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))).nonempty
  obtain ⟨q, hq⟩ := (hinf.sdiff ((finite_singleton (∞ :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).insert p)).nonempty
  have hpq : p ≠ q := by intro he; exact hq.2 (Or.inl he.symm)
  have hpne : p ≠ ∞ := fun he => hp.2 (mem_singleton_iff.mpr he)
  have hqne : q ≠ ∞ := fun he => hq.2 (Or.inr (mem_singleton_iff.mpr he))
  cases p using OnePoint.rec with
  | infty => exact False.elim (hpne rfl)
  | coe z =>
    cases q using OnePoint.rec with
    | infty => exact False.elim (hqne rfl)
    | coe w =>
      have hz := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary z).mp
        (realSL_limitSet_subset_halfPlaneIdealBoundary H hreal hp.1)
      have hw := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary w).mp
        (realSL_limitSet_subset_halfPlaneIdealBoundary H hreal hq.1)
      have hzr : z = (z.re : ℂ) := Complex.ext rfl hz
      have hwr : w = (w.re : ℂ) := Complex.ext rfl hw
      refine ⟨z.re, w.re, ?_, ?_, ?_⟩
      · intro he
        exact hpq (by rw [hzr, hwr, he])
      · rw [← hzr]
        exact hp.1
      · rw [← hwr]
        exact hq.1

/-- An ordinary complex neighborhood of a finite real endpoint has the expected real coordinate. -/
theorem halfPlaneBoundary_mem_complex_ball {p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hp : p ∈
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (u r : ℝ) (hU : p ∈ ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' Metric.ball (u : ℂ)
      r) :
    ∃ x : ℝ, p = ((x : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ |x - u| < r := by
  obtain ⟨z, hz, rfl⟩ := hU
  have hi := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary z).mp hp
  have he : z = (z.re : ℂ) := Complex.ext rfl hi
  refine ⟨z.re, congrArg ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) he, ?_⟩
  rw [he] at hz
  simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hz

/-- Two actual limit neighborhoods can be chosen with uniformly bounded separated real coordinates. -/
theorem realSL_limit_pair_neighborhoods (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hH :
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    (hreal : ∀ f ∈ H, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = f) :
    ∃ (U V : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (R δ : ℝ),
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      (U ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H).Nonempty ∧ (V ∩
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H).Nonempty ∧ 0 ≤ R ∧ 0 < δ ∧
      ∀ p ∈ U, ∀ q ∈ V, p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary → q ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary →
        ∃ x y : ℝ, p = ((x : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ q = ((y : ℂ) :
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
          |x| ≤ R ∧ |y| ≤ R ∧ δ ≤ |x - y| := by
  obtain ⟨u, v, huv, huL, hvL⟩ := realSL_limitSet_exists_real_pair H hH hreal
  let d := |u - v|
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr huv)
  let r := d / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let U := ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' Metric.ball (u : ℂ) r
  let V := ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' Metric.ball (v : ℂ) r
  have hdist : dist (u : ℂ) (v : ℂ) = d := by
    simp only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rfl
  have hUV : Disjoint U V := by
    apply Set.disjoint_image_of_injective OnePoint.coe_injective
    exact Metric.ball_disjoint_ball (by rw [hdist]; dsimp [r]; linarith)
  refine ⟨U, V, |u| + |v| + r, d / 2,
    OnePoint.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball,
    OnePoint.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball, hUV,
    ⟨((u : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨(u : ℂ), Metric.mem_ball_self hr, rfl⟩,
      huL⟩,
    ⟨((v : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨(v : ℂ), Metric.mem_ball_self hr, rfl⟩,
      hvL⟩,
    by positivity, by positivity, ?_⟩
  intro p hp q hq hpB hqB
  obtain ⟨x, hxp, hxu⟩ := halfPlaneBoundary_mem_complex_ball hpB u r hp
  obtain ⟨y, hyq, hyv⟩ := halfPlaneBoundary_mem_complex_ball hqB v r hq
  have hxabs : |x| ≤ |x - u| + |u| := by
    simpa only [sub_add_cancel] using abs_add_le (x - u) u
  have hyabs : |y| ≤ |y - v| + |v| := by
    simpa only [sub_add_cancel] using abs_add_le (y - v) v
  have hsep : d ≤ |x - u| + |x - y| + |y - v| := by
    have h := (abs_add_le (u - x) (x - y)).trans
      (le_refl (|u - x| + |x - y|))
    have ht := abs_add_le ((u - x) + (x - y)) (y - v)
    rw [show (u - x) + (x - y) + (y - v) = u - v by ring] at ht
    have hxrev : |u - x| = |x - u| := abs_sub_comm _ _
    dsimp [d]
    linarith
  refine ⟨x, y, hxp, hyq, ?_, ?_, ?_⟩
  · linarith [abs_nonneg v]
  · linarith [abs_nonneg u]
  · dsimp [r] at hxu hyv
    linarith

/-- Perfect endpoint density rules out bounded-trace replacements for every axis in a discrete real group. -/
theorem real_discrete_no_bounded_trace_replacements (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hreal : ∀ f ∈ H, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = f) :
    ¬ ∃ B : ℝ, ∀ f : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val →
      ∃ q : H, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic q.val ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints q.val f.val ∧
        ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace q.val‖ ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨U, V, R, δ, hU, hV, hUV, hUL, hVL, hR, hδ, hcoords⟩ :=
    realSL_limit_pair_neighborhoods H hH hreal
  let S : Set H := {q | _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic q.val ∧ ∃ x y : ℝ,
    |x| ≤ R ∧ |y| ≤ R ∧ δ ≤ |x - y| ∧
      q.val.val ((x : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (x : ℂ) ∧
      q.val.val ((y : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (y : ℂ) ∧
      ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace q.val‖ ≤ max B 0}
  have hS : S.Finite :=
    (discrete_realSL_bounded_fixed_pair_trace_finite H hd hreal R δ (max B 0)
      hR hδ (le_max_right _ _)).subset (fun _ h => h.2)
  let E : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⋃ q ∈ S, _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints q.val
  have hE : E.Finite := hS.biUnion fun q hq => by
    obtain ⟨a, b, _hab,
      hfix⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_loxodromic_boundary_fixed_pair q.val hq.1.1
    exact ((finite_singleton b).insert a).subset fun z hz => (hfix z).mp hz
  have hULinf := mobiusLimitSet_open_inter_infinite H hH U hU hUL
  obtain ⟨p, ⟨hpU, hpL⟩, hpE⟩ := (hULinf.sdiff hE).nonempty
  have hU' : IsOpen (U \ E) := hU.sdiff hE.isClosed
  have hUV' : Disjoint (U \ E) V := hUV.mono_left sdiff_subset
  have hUL' : ((U \ E) ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H).Nonempty := ⟨p, ⟨hpU,
    hpE⟩, hpL⟩
  obtain ⟨f, hfL, a, haU, b, hbV, hfa, hfb⟩ :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.exists_loxodromic_fixedPoints_in_disjoint_limit_neighbourhoods H hH (U \ E) V hU' hV hUV' hUL' hVL
  obtain ⟨A, hA⟩ := hreal f.val f.property
  have hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val := hA ▸ realSL_loxodromic_hyperbolic A (hA.symm ▸ hfL)
  obtain ⟨q, hq, hs, ht⟩ := hB f hf
  have haL : a ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨f, hfL, hfa⟩
  have hbL : b ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLoxodromicFixedPointSet_subset_limitSet H ⟨f, hfL, hfb⟩
  obtain ⟨x, y, hax, hby, hxR, hyR, hxy⟩ := hcoords a haU.1 b hbV
    (realSL_limitSet_subset_halfPlaneIdealBoundary H hreal haL)
    (realSL_limitSet_subset_halfPlaneIdealBoundary H hreal hbL)
  have hqa : q.val.val a = a := (hs a).mpr hfa
  have hqb : q.val.val b = b := (hs b).mpr hfb
  have hqS : q ∈ S := ⟨hq, x, y, hxR, hyR, hxy, by rwa [← hax], by rwa [← hby],
    ht.trans (le_max_left _ _)⟩
  have haE : a ∈ E := mem_iUnion_of_mem q (mem_iUnion_of_mem hqS hqa)
  exact haU.2 haE

/-- For literal actual maximal hyperbolic cyclic subgroup classes. -/
theorem fuchsian_maximal_hyperbolic_cyclic_conjugacy_infinite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (hH :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) :
    Infinite (FuchsianHyperbolicCyclicConjugacyClasses H) := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  have := hfinite
  obtain ⟨B, hB⟩ := finite_hyperbolic_classes_bounded_trace_same_fixedPoints D
  have hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary D.normalizedGroup := hH.conjugation D.halfPlaneNormalizer
  have hproperty := bounded_trace_same_fixedPoints_conjugation H D.halfPlaneNormalizer B hB
  exact real_discrete_no_bounded_trace_replacements D.normalizedGroup hNE D.normalizedGroup_discrete
    D.normalizedGroup_exists_realSL ⟨B, hproperty⟩

/-- In the original unbundled Fuchsian-group hypotheses. -/
theorem hyperbolic_cyclic_conjugacyClasses_infinite_of_nonElementary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hF : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup H) (hH :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) :
    Infinite (FuchsianHyperbolicCyclicConjugacyClasses H) := by
  obtain ⟨D⟩ := (fuchsianDisc_exists_iff H).mpr hF
  exact fuchsian_maximal_hyperbolic_cyclic_conjugacy_infinite D hH

end LowDimensionalTopology.Geometry.Fuchsian
