module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Conjugacy.ConjugacyClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianFiniteGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianPrimitives
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Fixed points are fixed by every integral power of the actual sphere action. -/
theorem mobius_zpow_fixed {f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {p :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hp : f.val p = p) (n : ℤ) : (f ^ n).val p = p := by
  cases n with
  | ofNat n =>
    change (f ^ (n : ℤ)).val p = p
    rw [zpow_natCast]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_pow_fixed hp n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_pow_fixed (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hp) (n + 1)

/-- Every nonidentity integral power has exactly the same full fixed set. -/
theorem mobius_zpow_same_fixedPoints (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (n : ℤ) (hn : f ^ n ≠ 1) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusSameFixedPoints f (f ^ n) := by
  obtain ⟨p, hp⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_has_boundary_fixed f hf
  have hc : Commute f (f ^ n) := Commute.self_zpow f n
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_commonFixedPoint_commutator_dichotomy f (f ^ n) hf hn ⟨p,
    hp, mobius_zpow_fixed hp n⟩ with
    ⟨_, _, hs⟩ | ⟨_, hnc, _⟩
  · exact hs
  · exact False.elim (hnc hc)

/-- The actual elliptic fixed point in an arbitrary preserved geometric disc is unique. -/
theorem elliptic_disc_existsUnique_fixed (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
  _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D) (hp : f.val '' D = D) :
    ∃! p : D, f.val p.val = p.val := by
  obtain ⟨q, hq⟩ := hD.normalize
  let F := q * f * q⁻¹
  have hF : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic F :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj (isConj_iff.mpr ⟨q, rfl⟩)).mp hf
  have hFp : F.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    rw [← hq]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image q f D).trans (congrArg (q.val '' ·)
      hp)
  obtain ⟨z, hz, hzu⟩ := elliptic_unitDisc_existsUnique_fixed F hF hFp
  have hzImage : z.val ∈ q.val '' D := by rw [hq]; exact z.property
  obtain ⟨p, hpD, hqp⟩ := hzImage
  have hpf : f.val p = p := by
    have hfix : F.val (q.val p) = q.val p := by simpa only [hqp] using hz
    change (q * f * q⁻¹).val (q.val p) = q.val p at hfix
    rwa [_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff,
      Equiv.symm_apply_apply] at hfix
  refine ⟨⟨p, hpD⟩, hpf, ?_⟩
  intro r hr
  have hqr : q.val r.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := hq ▸ mem_image_of_mem q.val r.property
  have hfr : F.val (q.val r.val) = q.val r.val := by
    change (q * f * q⁻¹).val (q.val r.val) = q.val r.val
    rwa [_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff, Equiv.symm_apply_apply]
  have he : (⟨q.val r.val, hqr⟩ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) = z := hzu _ hfr
  apply Subtype.ext
  apply q.val.injective
  exact (congrArg Subtype.val he).trans hqp.symm

/-- Cyclicity of the genuine point stabilizer forces its actual members to commute. -/
theorem fuchsian_fixed_stabilizer_commute {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (f g : H)
    (hf : f.val.val p = p) (hg : g.val.val p = p) : Commute f g := by
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p
  have : IsCyclic K := D.stabilizer_isCyclic p
  let F : K := ⟨f.val, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p
    f.val).mpr ⟨f.property, hf⟩⟩
  let G : K := ⟨g.val, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p
    g.val).mpr ⟨g.property, hg⟩⟩
  have hc : F * G = G * F := by
    obtain ⟨a, ha⟩ := exists_zpow_surjective K
    obtain ⟨m, hm⟩ := ha F
    obtain ⟨n, hn⟩ := ha G
    rw [← hm, ← hn]
    exact zpow_mul_comm a m n
  change f * g = g * f
  apply Subtype.ext
  exact congrArg (fun k : K => k.val) hc

/-- Conjugation transports the actual fixed point of an integral power. -/
theorem conjugator_zpowers_fixed {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (f h :
  H)
    (m n : ℤ) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp : f.val.val p = p)
    (hc : h * f ^ m * h⁻¹ = f ^ n) :
    (f.val ^ n).val (h.val.val p) = h.val.val p := by
  have he := congrArg (fun g : H => g.val.val (h.val.val p)) hc
  change h.val.val ((f.val ^ m).val (h.val.val.symm (h.val.val p))) =
    (f.val ^ n).val (h.val.val p) at he
  rw [Equiv.symm_apply_apply, mobius_zpow_fixed hp m] at he
  exact he.symm

/-- A conjugator of two powers must fix any common unique fixed point. -/
theorem conjugator_zpowers_unique_fixed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (f h : H)
    (m n : ℤ) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hp : f.val.val p = p)
    (hunique : ∀ z, (f.val ^ n).val z = z → z = p)
    (hc : h * f ^ m * h⁻¹ = f ^ n) : h.val.val p = p :=
  hunique _ (conjugator_zpowers_fixed f h m n p hp hc)

/-- Parabolic powers conjugate inside the original Fuchsian group are equal. -/
theorem fuchsian_parabolic_zpowers_isConj_iff_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (m n : ℤ) :
    IsConj (f ^ m) (f ^ n) ↔ f ^ m = f ^ n := by
  constructor
  · intro h
    by_cases hn : f ^ n = 1
    · rw [hn] at h
      exact (isConj_one_left.mp h).trans hn.symm
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    obtain ⟨p, hp⟩ := hf.2
    have hfp : f.val.val p = p := (hp p).mpr rfl
    have hnv : f.val ^ n ≠ 1 := by
      intro he
      exact hn (Subtype.ext he)
    have hsame := mobius_zpow_same_fixedPoints f.val hf.1 n hnv
    have hgp := conjugator_zpowers_unique_fixed f g m n p hfp
      (fun z hz => (hp z).mp ((hsame z).mpr hz)) hg
    have hc := fuchsian_fixed_stabilizer_commute D p g (f ^ m) hgp (mobius_zpow_fixed hfp m)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one] at hg
    exact hg
  · intro h
    rw [h]

/-- Elliptic powers conjugate inside the original Fuchsian group are equal as elements. -/
theorem fuchsian_elliptic_zpowers_isConj_iff_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val) (m n : ℤ) :
    IsConj (f ^ m) (f ^ n) ↔ f ^ m = f ^ n := by
  constructor
  · intro h
    by_cases hn : f ^ n = 1
    · rw [hn] at h
      exact (isConj_one_left.mp h).trans hn.symm
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    obtain ⟨p, hp, hpu⟩ := elliptic_disc_existsUnique_fixed f.val hf D.isDisc (D.image_eq f)
    have hnv : f.val ^ n ≠ 1 := by
      intro he
      exact hn (Subtype.ext he)
    have hsame := mobius_zpow_same_fixedPoints f.val hf.1 n hnv
    have hgp : g.val.val p.val = p.val := by
      have hgpD := D.invariant g p.val p.property
      have hfix := conjugator_zpowers_fixed f g m n p.val hp hg
      have hffix := (hsame (g.val.val p.val)).mpr hfix
      exact congrArg Subtype.val (hpu ⟨g.val.val p.val, hgpD⟩ hffix)
    have hc := fuchsian_fixed_stabilizer_commute D p.val g (f ^ m) hgp (mobius_zpow_fixed hp m)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one] at hg
    exact hg
  · intro h
    rw [h]

/-- The powers assertion following, with finite order interpreted as element equality. -/
theorem fuchsian_elliptic_or_parabolic_zpowers_isConj_iff_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (m n : ℤ) :
    IsConj (f ^ m) (f ^ n) ↔ f ^ m = f ^ n := by
  rcases hf with he | hp
  · exact fuchsian_elliptic_zpowers_isConj_iff_eq D f he m n
  · exact fuchsian_parabolic_zpowers_isConj_iff_eq D f hp m n

/-- Infinite parabolic order upgrades element equality to literal equality of integer exponents. -/
theorem fuchsian_parabolic_zpowers_isConj_iff_exponent_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) (m n : ℤ) :
    IsConj (f ^ m) (f ^ n) ↔ m = n := by
  rw [fuchsian_parabolic_zpowers_isConj_iff_eq D f hf]
  constructor
  · intro h
    have he : f.val ^ m = f.val ^ n := congrArg Subtype.val h
    exact (injective_zpow_iff_not_isOfFinOrder.mpr
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder f.val
        (Or.inl hf))) he
  · intro h
    rw [h]

/-- For finite elliptic order the exponents agree modulo the element order. -/
theorem fuchsian_elliptic_zpowers_isConj_iff_modEq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val) (m n : ℤ) :
    IsConj (f ^ m) (f ^ n) ↔ Int.ModEq (orderOf f) m n := by
  rw [fuchsian_elliptic_zpowers_isConj_iff_eq D f hf, zpow_eq_zpow_iff_modEq]

end LowDimensionalTopology.Geometry.Fuchsian
