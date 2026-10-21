/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.DihedralInvariantDiscs
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.PackingExample
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordFundamentalDomains
@[expose] public section
noncomputable section
open Set Monoid
open scoped Topology OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The open annulus between the two genuine dihedral fundamental circles. -/
def dihedralPackingAnnulus (d : ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  OnePoint.some '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < Real.sqrt d}

theorem coe_mem_dihedralPackingAnnulus (d : ℝ) (z : ℂ) :
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ dihedralPackingAnnulus d ↔ 1 < ‖z‖ ∧ ‖z‖ < Real.sqrt d := by
  simp [dihedralPackingAnnulus]

theorem dihedralPackingAnnulus_isOpen (d : ℝ) : IsOpen (dihedralPackingAnnulus d) :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))

theorem dihedral_annulus_log_bounds {d r : ℝ} (hd : 1 < d)
    (hr : 1 < r ∧ r < Real.sqrt d) : 0 < Real.log r ∧ Real.log r < Real.log d / 2 := by
  refine ⟨Real.log_pos hr.1, ?_⟩
  have h := Real.log_lt_log (by linarith only [hr.1]) hr.2
  rwa [Real.log_sqrt (by linarith only [hd])] at h

theorem dihedral_annulus_scale_exponent {d r s : ℝ} (hd : 1 < d)
    (hr : 1 < r ∧ r < Real.sqrt d) (hs : 1 < s ∧ s < Real.sqrt d) (n : ℤ)
    (he : s = d ^ n * r) : n = 0 := by
  have hd0 : 0 < d := by linarith only [hd]
  have hlog := congrArg Real.log he
  rw [Real.log_mul (zpow_pos hd0 n).ne' (by linarith only [hr.1] : r ≠ 0),
    Real.log_zpow] at hlog
  have hrlog := dihedral_annulus_log_bounds hd hr
  have hslog := dihedral_annulus_log_bounds hd hs
  have hdl := Real.log_pos hd
  by_contra hn
  rcases lt_or_gt_of_ne hn with hn | hn
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
    have hm := mul_le_mul_of_nonneg_right hn' hdl.le
    nlinarith only [hlog, hrlog.1, hrlog.2, hslog.1, hm]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Int.add_one_le_iff.mpr hn
    have hm := mul_le_mul_of_nonneg_right hn' hdl.le
    nlinarith only [hlog, hslog.2, hrlog.1, hm, hdl]

theorem dihedral_annulus_reciprocal_excluded {d r s : ℝ} (hd : 1 < d)
    (hr : 1 < r ∧ r < Real.sqrt d) (hs : 1 < s ∧ s < Real.sqrt d) (n : ℤ) :
    s ≠ d ^ n / r := by
  intro he
  have hd0 : 0 < d := by linarith only [hd]
  have hlog := congrArg Real.log he
  rw [Real.log_div (zpow_pos hd0 n).ne' (by linarith only [hr.1] : r ≠ 0),
    Real.log_zpow] at hlog
  have hrlog := dihedral_annulus_log_bounds hd hr
  have hslog := dihedral_annulus_log_bounds hd hs
  have hdl := Real.log_pos hd
  rcases le_or_gt n 0 with hn | hn
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    have hm := mul_nonpos_of_nonpos_of_nonneg hn' hdl.le
    linarith only [hlog, hrlog.1, hslog.1, hm]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Int.add_one_le_iff.mpr hn
    have hm := mul_le_mul_of_nonneg_right hn' hdl.le
    linarith only [hlog, hrlog.2, hslog.2, hm]

/-- Every nonidentity element of the actual infinite dihedral group separates the annulus. -/
theorem dihedralPackingAnnulus_isPacking (d : ℝ) (hd : 1 < d) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking (canonicalDihedralGroup d (by linarith)) (dihedralPackingAnnulus d) := by
  intro g hg
  apply Set.disjoint_left.mpr
  rintro w ⟨v, hv, rfl⟩ hw
  obtain ⟨z, hz, rfl⟩ := hv
  obtain ⟨n, hn | hn⟩ := (canonicalDihedralGroup_mem_iff d (by linarith) g.val).mp g.property
  · rw [hn, fuchsianPositiveDilation_coe] at hw
    have hw' := (coe_mem_dihedralPackingAnnulus d _).mp hw
    have hnorm : ‖(d ^ n : ℝ) * z‖ = d ^ n * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) n)]
    rw [hnorm] at hw'
    have hn0 := dihedral_annulus_scale_exponent hd hz hw' n rfl
    subst n
    apply hg
    apply Subtype.ext
    rw [hn, fuchsianPositiveDilation_zpow d (by linarith only [hd])]
    simp
  · have hz0 : z ≠ 0 := by
      intro he
      have h := hz.1
      rw [he, norm_zero] at h
      linarith only [h]
    rw [hn] at hw
    change (fuchsianPositiveDilation (d ^ n) (zpow_pos (by linarith only [hd]) n)).val (fuchsianDihedralFlip.val z) ∈ _ at hw
    rw [fuchsianDihedralFlip_coe z hz0, fuchsianPositiveDilation_coe] at hw
    have hw' := (coe_mem_dihedralPackingAnnulus d _).mp hw
    have hnorm : ‖(d ^ n : ℝ) * (-1 / z)‖ = d ^ n / ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) n),
        norm_div, norm_neg, norm_one, mul_one_div]
    rw [hnorm] at hw'
    exact dihedral_annulus_reciprocal_excluded hd hz hw' n rfl

/-- The closed double cone around the real axis, with its genuine ideal point. -/
def dihedralRealCone : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  insert ∞ (OnePoint.some '' {z : ℂ | |z.im| ≤ |z.re|})

theorem coe_mem_dihedralRealCone (z : ℂ) :
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ dihedralRealCone ↔ |z.im| ≤ |z.re| := by
  simp [dihedralRealCone]

theorem infty_mem_dihedralRealCone : ∞ ∈ dihedralRealCone := Set.mem_insert _ _

theorem dihedralRealCone_isClosed : IsClosed dihedralRealCone := by
  rw [OnePoint.isClosed_iff_of_mem infty_mem_dihedralRealCone]
  change IsClosed {z : ℂ | (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ dihedralRealCone}
  simp only [coe_mem_dihedralRealCone]
  exact isClosed_le Complex.continuous_im.abs Complex.continuous_re.abs

theorem fuchsianPositiveDilation_maps_dihedralRealCone (k : ℝ) (hk : 0 < k) :
    MapsTo (fuchsianPositiveDilation k hk).val dihedralRealCone dihedralRealCone := by
  intro z hz
  induction z using OnePoint.rec with
  | infty =>
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _).val ∞ ∈ _
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty]
    exact infty_mem_dihedralRealCone
  | coe z =>
    rw [fuchsianPositiveDilation_coe, coe_mem_dihedralRealCone]
    rw [coe_mem_dihedralRealCone] at hz
    simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero, abs_mul, abs_of_pos hk] using
      mul_le_mul_of_nonneg_left hz hk.le

theorem fuchsianDihedralFlip_maps_dihedralRealCone :
    MapsTo fuchsianDihedralFlip.val dihedralRealCone dihedralRealCone := by
  intro z hz
  induction z using OnePoint.rec with
  | infty =>
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
      (-1)).val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val ∞) ∈ _
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_infty,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero, coe_mem_dihedralRealCone]
    simp
  | coe z =>
    by_cases hz0 : z = 0
    · subst z
      change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
        (-1)).val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val (0 : ℂ)) ∈ _
      rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_zero,
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty]
      exact infty_mem_dihedralRealCone
    · rw [fuchsianDihedralFlip_coe z hz0, coe_mem_dihedralRealCone]
      rw [coe_mem_dihedralRealCone] at hz
      have hN := Complex.normSq_pos.mpr hz0
      simpa [neg_div, Complex.inv_re, Complex.inv_im, abs_div, abs_of_pos hN] using
        (div_le_div_iff_of_pos_right hN).mpr hz

theorem canonicalDihedralGroup_maps_dihedralRealCone (d : ℝ) (hd : 0 < d)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g ∈ canonicalDihedralGroup d hd) :
    MapsTo g.val dihedralRealCone dihedralRealCone := by
  obtain ⟨n, rfl | rfl⟩ := (canonicalDihedralGroup_mem_iff d hd g).mp hg
  · exact fuchsianPositiveDilation_maps_dihedralRealCone _ _
  · exact (fuchsianPositiveDilation_maps_dihedralRealCone (d ^ n) (zpow_pos hd n)).comp
      fuchsianDihedralFlip_maps_dihedralRealCone

/-- A genuine positive affine change of coordinates, preserving the real half-plane. -/
def packingParabolicChart (p ε : ℝ) (hε : 0 < ε) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (p : ℂ) * fuchsianPositiveDilation ε hε

theorem packingParabolicChart_coe (p ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    (packingParabolicChart p ε hε).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      (((ε : ℂ) * z + (p : ℂ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (p :
    ℂ)).val ((fuchsianPositiveDilation ε hε).val z) = _
  rw [fuchsianPositiveDilation_coe, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]

theorem packingParabolicChart_infty (p ε : ℝ) (hε : 0 < ε) :
    (packingParabolicChart p ε hε).val ∞ = ∞ := by
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (p :
    ℂ)).val ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _).val ∞) = ∞
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]

/-- The actual conjugate parabolic and its open two-disc exterior. -/
def packingLocalizedParabolic (p ε : ℝ) (hε : 0 <
  ε) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  packingParabolicChart p ε hε * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGenerator * (packingParabolicChart p ε hε)⁻¹

def packingLocalizedDomain (p ε : ℝ) (hε : 0 < ε) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  (packingParabolicChart p ε hε).val '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondDomain

theorem packingLocalizedDomain_isOpen (p ε : ℝ) (hε : 0 < ε) :
    IsOpen (packingLocalizedDomain p ε hε) :=
  (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph (packingParabolicChart p ε hε)).isOpenMap _
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondDomain_isOpen

theorem packingLocalizedDomain_isPacking (p ε : ℝ) (hε : 0 < ε) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking (Subgroup.zpowers (packingLocalizedParabolic p
      ε hε))
      (packingLocalizedDomain p ε hε) := by
  have he : Subgroup.zpowers (packingLocalizedParabolic p ε hε) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (packingParabolicChart p ε hε) _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGroup := by
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGroup, MonoidHom.map_zpowers]
    rfl
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondDomain_isPacking.conjugation _

theorem packingLocalizedDomain_infty (p ε : ℝ) (hε : 0 < ε) :
    ∞ ∈ packingLocalizedDomain p ε hε :=
  ⟨∞, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.infty_mem_packingSecondDomain, packingParabolicChart_infty p
    ε hε⟩

/-- The conjugate strip is literally the common exterior of the two tangent circles. -/
theorem coe_mem_packingLocalizedDomain (p ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ packingLocalizedDomain p ε hε ↔
      ε < ‖z - ((p - ε : ℝ) : ℂ)‖ ∧ ε < ‖z - ((p + ε : ℝ) : ℂ)‖ := by
  have hchart (v : ℂ) :
      ((((ε : ℂ) * v + (p : ℂ) : ℂ)) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ packingLocalizedDomain p ε hε ↔
        ε < ‖(ε : ℂ) * v + (p : ℂ) - ((p - ε : ℝ) : ℂ)‖ ∧
        ε < ‖(ε : ℂ) * v + (p : ℂ) - ((p + ε : ℝ) : ℂ)‖ := by
    rw [← packingParabolicChart_coe p ε hε v]
    change (packingParabolicChart p ε hε).val (v : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈
      (packingParabolicChart p ε
        hε).val '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondDomain ↔ _
    rw [Set.mem_image_equiv, Equiv.symm_apply_apply,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.coe_mem_packingSecondDomain]
    have he₁ : (ε : ℂ) * v + (p : ℂ) - ((p - ε : ℝ) : ℂ) = (ε : ℂ) * (v + 1) := by
      push_cast
      ring
    have he₂ : (ε : ℂ) * v + (p : ℂ) - ((p + ε : ℝ) : ℂ) = (ε : ℂ) * (v - 1) := by
      push_cast
      ring
    rw [he₁, he₂, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    exact and_congr (lt_mul_iff_one_lt_right hε).symm (lt_mul_iff_one_lt_right hε).symm
  let v : ℂ := (z - (p : ℂ)) / (ε : ℂ)
  have he : (ε : ℂ) * v + (p : ℂ) = z := by
    dsimp only [v]
    field_simp [Complex.ofReal_ne_zero.mpr hε.ne']
    ring
  simpa only [he] using hchart v

/-- Both genuine closed bad discs have their common tangency point on the positive real axis. -/
theorem packingLocalizedDomain_compl_eq (p ε : ℝ) (hε : 0 < ε) :
    (packingLocalizedDomain p ε hε)ᶜ = OnePoint.some ''
      (Metric.closedBall (((p - ε : ℝ) : ℂ)) ε ∪ Metric.closedBall (((p + ε : ℝ) : ℂ)) ε) := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [packingLocalizedDomain_infty]
  | coe z =>
    simp only [Set.mem_compl_iff, coe_mem_packingLocalizedDomain, Set.mem_image,
      OnePoint.coe_eq_coe, exists_eq_right, Set.mem_union, Metric.mem_closedBall, dist_eq_norm]
    exact not_and_or.trans (or_congr not_lt not_lt)

/-- The complement consists of two small tangent discs, so every point is within twice
 the affine scale of their common tangency point. This estimate includes infinity. -/
theorem packingLocalizedDomain_compl_bound (p ε : ℝ) (hε : 0 < ε)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : z ∉ packingLocalizedDomain p ε hε) :
    ∃ u : ℂ, (u : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z ∧ ‖u - (p : ℂ)‖ ≤ 2 * ε := by
  let q := packingParabolicChart p ε hε
  obtain ⟨v, he⟩ := q.val.surjective z
  have hv : v ∉ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondDomain := fun h => hz ⟨v, h, he⟩
  induction v using OnePoint.rec with
  | infty => exact (hv _root_.LowDimensionalTopology.Geometry.DiscreteGroups.infty_mem_packingSecondDomain).elim
  | coe v =>
    have hv' : ‖v + 1‖ ≤ 1 ∨ ‖v - 1‖ ≤ 1 := by
      simpa only [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.coe_mem_packingSecondDomain, not_and_or,
        not_lt] using hv
    have hnorm : ‖v‖ ≤ 2 := by
      rcases hv' with hv' | hv'
      · have h := norm_sub_le (v + 1) (1 : ℂ)
        rw [add_sub_cancel_right, norm_one] at h
        linarith only [h, hv']
      · have h := norm_add_le (v - 1) (1 : ℂ)
        rw [sub_add_cancel, norm_one] at h
        linarith only [h, hv']
    refine ⟨(ε : ℂ) * v + (p : ℂ), ?_, ?_⟩
    · exact (packingParabolicChart_coe p ε hε v).symm.trans he
    · rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      nlinarith only [hnorm, hε]

/-- The genuine small-disc localization follows from an open neighborhood of a positive
 real tangency point; the parabolic scale is chosen, rather than assumed to exist. -/
theorem exists_packingLocalizedDomain_compl_subset (d : ℝ) (hd : 1 < d) :
    ∃ p ε : ℝ, ∃ hε : 0 < ε, 1 < p ∧ p < Real.sqrt d ∧
      (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone := by
  have hsqrt : 1 < Real.sqrt d := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hd
    simpa using h
  let p := (1 + Real.sqrt d) / 2
  have hp1 : 1 < p := by dsimp only [p]; linarith only [hsqrt]
  have hp2 : p < Real.sqrt d := by dsimp only [p]; linarith only [hsqrt]
  have hp0 : 0 < p := by linarith only [hp1]
  let U : Set ℂ := {z | 1 < ‖z‖ ∧ ‖z‖ < Real.sqrt d ∧ |z.im| < |z.re|}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter
      ((isOpen_lt continuous_norm continuous_const).inter
        (isOpen_lt Complex.continuous_im.abs Complex.continuous_re.abs))
  have hpU : (p : ℂ) ∈ U := by
    change 1 < ‖(p : ℂ)‖ ∧ ‖(p : ℂ)‖ < Real.sqrt d ∧ |(p : ℂ).im| < |(p : ℂ).re|
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0] using ⟨hp1, hp2, hp0⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU (p : ℂ) hpU
  let ε := δ / 4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨p, ε, hε, hp1, hp2, ?_⟩
  intro z hz
  obtain ⟨u, rfl, hu⟩ := packingLocalizedDomain_compl_bound p ε hε z hz
  have huU : u ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖u - (p : ℂ)‖ ≤ 2 * ε := hu
      _ < δ := by dsimp only [ε]; linarith only [hδ]
  refine ⟨(coe_mem_dihedralPackingAnnulus d u).mpr ⟨huU.1, huU.2.1⟩,
    (coe_mem_dihedralRealCone u).mpr huU.2.2.le⟩

theorem dihedralPacking_domains_cover (d p ε : ℝ) (hε : 0 < ε)
    (hloc : (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone) :
    dihedralPackingAnnulus d ∪ packingLocalizedDomain p ε hε = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : z ∈ packingLocalizedDomain p ε hε
  · exact Or.inr hz
  · exact Or.inl (hloc hz).1

theorem dihedralPacking_common_nonempty (d p ε : ℝ) (hε : 0 < ε)
    (hp : 1 < p) (hp' : p < Real.sqrt d)
    (hloc : (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone) :
    (dihedralPackingAnnulus d ∩ packingLocalizedDomain p ε hε).Nonempty := by
  let z : ℂ := (p : ℂ) * Complex.I
  have hp0 : 0 < p := by linarith only [hp]
  have hzA : (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ dihedralPackingAnnulus d := by
    rw [coe_mem_dihedralPackingAnnulus]
    simpa [z, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0] using ⟨hp, hp'⟩
  have hzC : (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∉ dihedralRealCone := by
    rw [coe_mem_dihedralRealCone]
    simp only [z, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      abs_zero, abs_of_pos hp0, not_le]
    exact hp0
  exact ⟨z, hzA, by_contra (fun hz => hzC (hloc hz).2)⟩

theorem packingSecondGenerator_mem_realSL_range : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGenerator ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![1, 0; 1, 1], by norm_num⟩
  refine ⟨A, ?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGenerator_projection]
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom A)) = _
  congr 1
  apply Units.ext
  ext i j
  change ((A.val i j : ℝ) : ℂ) = _
  fin_cases i <;> fin_cases j <;> norm_num [A, _root_.LowDimensionalTopology.Geometry.Mobius.coefficientMatrix]

theorem packingParabolicChart_mem_realSL_range (p ε : ℝ) (hε : 0 < ε) :
    packingParabolicChart p ε hε ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range.mul_mem
  · refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL p, ?_⟩
    apply mobius_ext_on_halfPlane
    intro z
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
  · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL ε hε, realSLMobius_verticalDilation ε
    hε⟩

theorem packingLocalizedParabolic_mem_realSL_range (p ε : ℝ) (hε : 0 < ε) :
    packingLocalizedParabolic p ε hε ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range.mul_mem
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range.mul_mem
      (packingParabolicChart_mem_realSL_range p ε hε)
      packingSecondGenerator_mem_realSL_range)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range.inv_mem
      (packingParabolicChart_mem_realSL_range p ε hε))

theorem packingLocalizedParabolic_parabolic (p ε : ℝ) (hε : 0 < ε) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (packingLocalizedParabolic p ε hε) := by
  have hT : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero
  have hS : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGenerator :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨_root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius, rfl⟩)).mp hT
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj
    (isConj_iff.mpr ⟨packingParabolicChart p ε hε, rfl⟩)).mp hS

theorem packingLocalizedParabolic_fixes (p ε : ℝ) (hε : 0 < ε) :
    (packingLocalizedParabolic p ε hε).val (p : ℂ) = (p : ℂ) := by
  have hzero : (packingParabolicChart p ε hε).val (0 : ℂ) = (p : ℂ) := by
    rw [packingParabolicChart_coe]
    simp
  rw [← hzero]
  change (packingParabolicChart p ε hε).val
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGenerator.val ((packingParabolicChart p ε
      hε).val.symm
      ((packingParabolicChart p ε hε).val (0 : ℂ)))) = _
  rw [Equiv.symm_apply_apply, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGenerator_coe]
  norm_num

/-- Literal actual factors, retaining the prescribed dihedral subgroup. -/
def dihedralParabolicFactors (d : ℝ) (hd : 0 < d) (p ε : ℝ) (hε : 0 < ε) :
    Bool → Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  fun b => if b then Subgroup.zpowers (packingLocalizedParabolic p ε hε)
    else canonicalDihedralGroup d hd

def dihedralParabolicDomains (d p ε : ℝ) (hε : 0 <
  ε) : Bool → Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  fun b => if b then packingLocalizedDomain p ε hε else dihedralPackingAnnulus d

def dihedralParabolicGroup (d : ℝ) (hd : 0 < d) (p ε : ℝ) (hε : 0 < ε) :
    Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := ⨆ b, dihedralParabolicFactors d hd p ε hε b

theorem dihedralParabolicGroup_discrete (d : ℝ) (hd : 1 < d) (p ε : ℝ) (hε : 0 < ε)
    (hp : 1 < p) (hp' : p < Real.sqrt d)
    (hloc : (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone) :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (dihedralParabolicGroup d (by linarith) p ε hε) := by
  have hpack (b : Bool) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking (dihedralParabolicFactors d (by linarith) p ε hε b)
      (dihedralParabolicDomains d p ε hε b) := by
    cases b
    · exact dihedralPackingAnnulus_isPacking d hd
    · exact packingLocalizedDomain_isPacking p ε hε
  have hcover (i j : Bool) (hij : i ≠ j) :
      dihedralParabolicDomains d p ε hε i ∪ dihedralParabolicDomains d p ε hε j = Set.univ := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact dihedralPacking_domains_cover d p ε hε hloc
    · rw [union_comm]
      exact dihedralPacking_domains_cover d p ε hε hloc
    · exact (hij rfl).elim
  have hcommon : (⋂ b, dihedralParabolicDomains d p ε hε b).Nonempty := by
    obtain ⟨z, hzA, hzB⟩ := dihedralPacking_common_nonempty d p ε hε hp hp' hloc
    refine ⟨z, Set.mem_iInter.mpr ?_⟩
    intro b
    cases b
    · exact hzA
    · exact hzB
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPacking_generated_discrete _ _ hpack hcover hcommon
  apply isOpen_iInter_of_finite
  intro b
  cases b
  · exact dihedralPackingAnnulus_isOpen d
  · exact packingLocalizedDomain_isOpen p ε hε

theorem dihedralParabolicGroup_preserves_halfPlane (d : ℝ) (hd : 0 < d)
    (p ε : ℝ) (hε : 0 < ε) (g : dihedralParabolicGroup d hd p ε hε) :
    g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have hrange : dihedralParabolicGroup d hd p ε hε ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
    apply iSup_le
    intro b
    cases b
    · change Subgroup.closure _ ≤ _
      apply (Subgroup.closure_le _).mpr
      intro f hf
      rcases (show f = fuchsianPositiveDilation d hd ∨ f = fuchsianDihedralFlip by simpa using hf) with
        rfl | rfl
      · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL d hd, realSLMobius_verticalDilation
        d hd⟩
      · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one,
        dihedralFlip_realSL_projection⟩
    · apply Subgroup.zpowers_le.mpr
      exact packingLocalizedParabolic_mem_realSL_range p ε hε
  obtain ⟨A, hA⟩ := hrange g.property
  rw [← hA]
  exact realSLMobius_image_openHalfPlane A

/-- The actual generated group is Fuchsian in the original half-plane model. -/
theorem dihedralParabolicFuchsianGroup (d : ℝ) (hd : 1 < d) (p ε : ℝ) (hε : 0 < ε)
    (hp : 1 < p) (hp' : p < Real.sqrt d)
    (hloc : (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone) :
    HalfPlaneFuchsianGroup (dihedralParabolicGroup d (by linarith) p ε hε) where
  preserves := dihedralParabolicGroup_preserves_halfPlane d (by linarith) p ε hε
  discrete := dihedralParabolicGroup_discrete d hd p ε hε hp hp' hloc

theorem packingTranslation_positive_periodic (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (m :
  ℕ) (hm : 0 < m)
    (hz : ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) ^ m).val z = z) : z = ∞ := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z =>
    have he : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) ^ m = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (m : ℂ) := by
      rw [← zpow_natCast, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingTranslation_zpow]
      simp
    rw [he, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe, OnePoint.coe_eq_coe] at hz
    have hm0 : (m : ℂ) = 0 := add_left_cancel (hz.trans (add_zero z).symm)
    exact (hm.ne' (Nat.cast_eq_zero.mp hm0)).elim

theorem packingLocalizedParabolic_positive_periodic (p ε : ℝ) (hε : 0 < ε)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (m : ℕ) (hm : 0 < m)
    (hz : ((packingLocalizedParabolic p ε hε) ^ m).val z = z) : z = (p : ℂ) := by
  let q := packingParabolicChart p ε hε * _root_.LowDimensionalTopology.Geometry.Mobius.reciprocalMobius
  have hf : packingLocalizedParabolic p ε hε = q * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 * q⁻¹ := by
    simp only [packingLocalizedParabolic, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingSecondGenerator,
      q, mul_inv_rev]
    group
  have hq : q.val ∞ = (p : ℂ) := by
    change (packingParabolicChart p ε hε).val (_root_.LowDimensionalTopology.Geometry.Mobius.reciprocal ∞) = _
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.reciprocal_infty, packingParabolicChart_coe]
    simp
  have hperiod : ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) ^ m).val (q.val.symm z) = q.val.symm z := by
    apply q.val.injective
    rw [Equiv.apply_symm_apply]
    change (q * (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) ^ m * q⁻¹).val z = z
    rw [← conj_pow, ← hf]
    exact hz
  have hz' := packingTranslation_positive_periodic (q.val.symm z) m hm hperiod
  calc
    z = q.val (q.val.symm z) := (q.val.apply_symm_apply z).symm
    _ = q.val ∞ := congrArg q.val hz'
    _ = (p : ℂ) := hq

theorem dihedralParabolicGroup_nonElementary (d : ℝ) (hd : 1 < d)
    (p ε : ℝ) (hε : 0 < ε) (hp : 1 < p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (dihedralParabolicGroup d (by linarith) p ε hε) := by
  let H := dihedralParabolicGroup d (by linarith) p ε hε
  let f := packingLocalizedParabolic p ε hε
  let a := fuchsianPositiveDilation d (by linarith only [hd])
  have hfH : f ∈ H := by
    apply (le_iSup (dihedralParabolicFactors d (by linarith) p ε hε) true)
    exact Subgroup.mem_zpowers f
  have haH : a ∈ H := by
    apply (le_iSup (dihedralParabolicFactors d (by linarith) p ε hε) false)
    exact Subgroup.subset_closure (by simp [a])
  intro he
  rcases (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_iff_boundary_or_interior H).mp he with ⟨z,
    hz⟩ | ⟨q, hq⟩
  · let fH : H := ⟨f, hfH⟩
    let aH : H := ⟨a, haH⟩
    obtain ⟨m, hm, hfix⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit z hz fH
    have hzfix : z = (p : ℂ) := packingLocalizedParabolic_positive_periodic p ε hε z m hm
      (hfix z (MulAction.mem_orbit_self z))
    have hazfix : aH • z = (p : ℂ) :=
      packingLocalizedParabolic_positive_periodic p ε hε (aH • z) m hm
        (hfix (aH • z) (MulAction.mem_orbit z aH))
    rw [hzfix] at hazfix
    change a.val (p : ℂ) = (p : ℂ) at hazfix
    rw [fuchsianPositiveDilation_coe, OnePoint.coe_eq_coe] at hazfix
    have he' := congrArg Complex.re hazfix
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at he'
    nlinarith only [he', hd, hp]
  · have hpar := packingLocalizedParabolic_parabolic p ε hε
    have hell := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_H3_orbit_all_elliptic H q hq f hfH hpar.1
    exact hell.not_parabolic hpar

/-- A reduced word containing the second factor enters the invariant cone.
The assertion is proved from genuine reduced words, with no orbit-trapping hypothesis. -/
theorem mobiusPacking_reduced_word_cone
    (G : Bool → Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D : Bool → Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (C : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp : ∀ i,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking (G i) (D i))
    (hc : ∀ i j, i ≠ j → D i ∪ D j = Set.univ)
    (hC : ∀ g ∈ G false, ∀ z ∈ C, g.val z ∈ C)
    (hsecond : ∀ g : G true, g ≠ 1 → ∀ z ∈ D true, g.val.val z ∈ C)
    {i j : Bool} (w : CoprodI.NeWord (fun i => G i) i j) :
    ∀ z ∈ D j, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G w.prod).val z ∈ C ∨
      (i = false ∧ j = false ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G w.prod ∈ G false) := by
  induction w with
  | @singleton i g hg =>
    intro z hz
    cases i with
    | false => exact Or.inr ⟨rfl, rfl, g.property⟩
    | true => exact Or.inl (hsecond g hg z hz)
  | @append i j k l w₁ hne w₂ ih₁ ih₂ =>
    intro z hz
    have hnot := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPacking_reduced_word G D hp hc w₂ z hz
    have hin : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G w₂.prod).val z ∈ D j := by
      have hm : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G w₂.prod).val z ∈ D j ∪ D k := by
        rw [hc j k hne]
        trivial
      exact hm.resolve_right hnot
    have hleft := ih₁ _ hin
    have hright := ih₂ z hz
    rw [CoprodI.NeWord.append_prod, map_mul]
    change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G w₁.prod).val
      ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G w₂.prod).val z) ∈ C ∨ _
    rcases hleft with hleft | ⟨hi, hj, hleft⟩
    · exact Or.inl hleft
    · rcases hright with hright | ⟨hk, hl, hright⟩
      · exact Or.inl (hC _ hleft _ hright)
      · exact (hne (hj.trans hk.symm)).elim

/-- The whole generated group has the actual orbit dichotomy inherited from its reduced words. -/
theorem mobiusPacking_generated_orbit_cone
    (G : Bool → Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D : Bool → Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (C : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hp : ∀ i,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking (G i) (D i))
    (hc : ∀ i j, i ≠ j → D i ∪ D j = Set.univ)
    (hC : ∀ g ∈ G false, ∀ z ∈ C, g.val z ∈ C)
    (hsecond : ∀ g : G true, g ≠ 1 → ∀ z ∈ D true, g.val.val z ∈ C)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : z ∈ ⋂ i, D i)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g ∈ ⨆ i, G i) :
    g.val z ∈ C ∨ ∃ a ∈ G false, a.val z = g.val z := by
  classical
  obtain ⟨x, hx⟩ := (show g ∈ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G).range by
    rwa [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift_range])
  let w := CoprodI.Word.equiv x
  have hwprod : w.prod = x := (CoprodI.Word.equiv).symm_apply_apply x
  by_cases hw : w = CoprodI.Word.empty
  · have hg1 : g = 1 := by rw [← hx, ← hwprod, hw, CoprodI.Word.prod_empty, map_one]
    exact Or.inr ⟨1, (G false).one_mem, by rw [hg1]⟩
  · obtain ⟨i, j, v, hv⟩ := CoprodI.NeWord.of_word w hw
    have hvprod : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G v.prod = g := by
      change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPackingFreeProductLift G v.toWord.prod = g
      rw [hv, hwprod]
      exact hx
    have hvC := mobiusPacking_reduced_word_cone G D C hp hc hC hsecond v z
      (Set.mem_iInter.mp hz j)
    rw [hvprod] at hvC
    exact hvC.imp_right (fun h => ⟨g, h.2.2, rfl⟩)

/-- The specialized orbit trapping is derived from the two actual packing domains. -/
theorem dihedralParabolicGroup_orbit_cone (d : ℝ) (hd : 1 < d)
    (p ε : ℝ) (hε : 0 < ε)
    (hloc : (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hzA : z ∈ dihedralPackingAnnulus d) (hzC : z ∉
      dihedralRealCone)
    (g : dihedralParabolicGroup d (by linarith) p ε hε) :
    g.val.val z ∈ dihedralRealCone ∨
      ∃ a ∈ canonicalDihedralGroup d (by linarith), a.val z = g.val.val z := by
  have hpack (b : Bool) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking (dihedralParabolicFactors d (by linarith) p ε hε b)
      (dihedralParabolicDomains d p ε hε b) := by
    cases b
    · exact dihedralPackingAnnulus_isPacking d hd
    · exact packingLocalizedDomain_isPacking p ε hε
  have hcover (i j : Bool) (hij : i ≠ j) :
      dihedralParabolicDomains d p ε hε i ∪ dihedralParabolicDomains d p ε hε j = Set.univ := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact dihedralPacking_domains_cover d p ε hε hloc
    · rw [union_comm]
      exact dihedralPacking_domains_cover d p ε hε hloc
    · exact (hij rfl).elim
  have hzB : z ∈ packingLocalizedDomain p ε hε := by
    by_contra h
    exact hzC (hloc h).2
  have hz : z ∈ ⋂ b, dihedralParabolicDomains d p ε hε b := by
    apply Set.mem_iInter.mpr
    intro b
    cases b
    · exact hzA
    · exact hzB
  apply mobiusPacking_generated_orbit_cone _ _ _ hpack hcover ?_ ?_ z hz g.val g.property
  · exact fun a ha => canonicalDihedralGroup_maps_dihedralRealCone d (by linarith) a ha
  · intro a ha v hv
    have hvout : a.val.val v ∉ packingLocalizedDomain p ε hε := by
      intro h
      exact Set.disjoint_left.mp (packingLocalizedDomain_isPacking p ε hε a ha) ⟨v, hv, rfl⟩ h
    exact (hloc hvout).2

/-- The actual common packing gives trivial point stabilizers for both selected centers. -/
theorem dihedralParabolicGroup_fixing_annulus_point (d : ℝ) (hd : 1 < d)
    (p ε : ℝ) (hε : 0 < ε)
    (hloc : (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hzA : z ∈ dihedralPackingAnnulus d) (hzC : z ∉
      dihedralRealCone)
    (g : dihedralParabolicGroup d (by linarith) p ε hε) (hfix : g.val.val z = z) : g = 1 := by
  have hpack (b : Bool) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking (dihedralParabolicFactors d (by linarith) p ε hε b)
      (dihedralParabolicDomains d p ε hε b) := by
    cases b
    · exact dihedralPackingAnnulus_isPacking d hd
    · exact packingLocalizedDomain_isPacking p ε hε
  have hcover (i j : Bool) (hij : i ≠ j) :
      dihedralParabolicDomains d p ε hε i ∪ dihedralParabolicDomains d p ε hε j = Set.univ := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact dihedralPacking_domains_cover d p ε hε hloc
    · rw [union_comm]
      exact dihedralPacking_domains_cover d p ε hε hloc
    · exact (hij rfl).elim
  have hz : z ∈ ⋂ b, dihedralParabolicDomains d p ε hε b := by
    apply Set.mem_iInter.mpr
    intro b
    cases b
    · exact hzA
    · by_contra h
      exact hzC (hloc h).2
  by_contra hg
  exact Set.disjoint_left.mp (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusPacking_common_intersection _
    _ hpack hcover g hg)
    ⟨z, hz, hfix⟩ hz

theorem dihedralParabolicGroup_eq_sup (d : ℝ) (hd : 0 < d)
    (p ε : ℝ) (hε : 0 < ε) : dihedralParabolicGroup d hd p ε hε =
      canonicalDihedralGroup d hd ⊔ Subgroup.zpowers (packingLocalizedParabolic p ε hε) := by
  apply le_antisymm
  · apply iSup_le
    intro b
    cases b
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup (dihedralParabolicFactors d hd p ε hε) false)
      (le_iSup (dihedralParabolicFactors d hd p ε hε) true)

theorem canonicalDihedralGroup_le_dihedralParabolicGroup (d : ℝ) (hd : 0 < d)
    (p ε : ℝ) (hε : 0 < ε) :
    canonicalDihedralGroup d hd ≤ dihedralParabolicGroup d hd p ε hε :=
  le_iSup (dihedralParabolicFactors d hd p ε hε) false

/-- Every prescribed dihedral annulus admits an actual non-elementary Fuchsian extension
 with the required orbit dichotomy; all localization conditions are constructed. -/
theorem exists_dihedralParabolicPacking (d : ℝ) (hd : 1 < d) :
    ∃ p ε : ℝ, ∃ hε : 0 < ε, 1 < p ∧ p < Real.sqrt d ∧
      (packingLocalizedDomain p ε hε)ᶜ ⊆ dihedralPackingAnnulus d ∩ dihedralRealCone ∧
      HalfPlaneFuchsianGroup (dihedralParabolicGroup d (by linarith) p ε hε) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (dihedralParabolicGroup d (by linarith) p ε hε) ∧
      ∀ z ∈ dihedralPackingAnnulus d, z ∉ dihedralRealCone →
        (∀ g : dihedralParabolicGroup d (by linarith) p ε hε,
          g.val.val z ∈ dihedralRealCone ∨
            ∃ a ∈ canonicalDihedralGroup d (by linarith), a.val z = g.val.val z) ∧
        (∀ g : dihedralParabolicGroup d (by linarith) p ε hε, g.val.val z = z → g = 1) := by
  obtain ⟨p, ε, hε, hp, hp', hloc⟩ := exists_packingLocalizedDomain_compl_subset d hd
  refine ⟨p, ε, hε, hp, hp', hloc,
    dihedralParabolicFuchsianGroup d hd p ε hε hp hp' hloc,
    dihedralParabolicGroup_nonElementary d hd p ε hε hp, ?_⟩
  intro z hzA hzC
  exact ⟨dihedralParabolicGroup_orbit_cone d hd p ε hε hloc z hzA hzC,
    dihedralParabolicGroup_fixing_annulus_point d hd p ε hε hloc z hzA hzC⟩

end LowDimensionalTopology.Geometry.Fuchsian
