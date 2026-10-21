module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc ENNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Angular Haar measure is monotone for literal subsets of the native disc. -/
theorem discSubtendedAngularFraction_mono {S T : Set Complex.UnitDisc}
    (h : S⊆T) (z : Complex.UnitDisc) :
    discSubtendedAngularFraction S z≤discSubtendedAngularFraction T z :=
  measure_mono (discRadialDirections_mono (image_mono h))

/-- The actual angular fraction of the germ at the point. Taking all genuine
neighborhoods removes distant parts of a possibly nonconvex original polygon. -/
def discLocalAngularFraction (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) : ℝ≥0∞ :=
  ⨅ N : {N : Set Complex.UnitDisc // N∈𝓝 z},discSubtendedAngularFraction (S∩N.val) z

/-- Local subtended angle in radians, with the usual full angle normalization. -/
def discLocalAngle (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) : ℝ :=
  2*Real.pi*(discLocalAngularFraction S z).toReal

theorem discLocalAngularFraction_le (S : Set Complex.UnitDisc) (z : Complex.UnitDisc)
    (N : Set Complex.UnitDisc) (hN : N∈𝓝 z) :
    discLocalAngularFraction S z≤discSubtendedAngularFraction (S∩N) z :=
  iInf_le (fun M : {N : Set Complex.UnitDisc // N∈𝓝 z} =>
    discSubtendedAngularFraction (S∩M.val) z) ⟨N,hN⟩

theorem discLocalAngularFraction_mono {S T : Set Complex.UnitDisc} (h : S⊆T)
    (z : Complex.UnitDisc) : discLocalAngularFraction S z≤discLocalAngularFraction T z := by
  apply iInf_mono
  intro N
  exact discSubtendedAngularFraction_mono (inter_subset_inter_left _ h) z

/-- The germ angle depends only on the actual set in an actual neighborhood. -/
theorem discLocalAngularFraction_congr {S T : Set Complex.UnitDisc} {z : Complex.UnitDisc}
    (h : ∀ᶠ w in 𝓝 z,w∈S ↔w∈T) : discLocalAngularFraction S z=discLocalAngularFraction T z := by
  have step {A B : Set Complex.UnitDisc}
      (he : ∀ᶠ w in 𝓝 z,w∈A ↔w∈B) :
      discLocalAngularFraction A z≤discLocalAngularFraction B z := by
    apply le_iInf
    intro N
    have hn : N.val∩{w | w∈A ↔w∈B}∈𝓝 z:=inter_mem N.property he
    apply (discLocalAngularFraction_le A z _ hn).trans
    apply discSubtendedAngularFraction_mono
    rintro w ⟨hwA,hwN,hw⟩
    exact ⟨hw.mp hwA,hwN⟩
  exact le_antisymm (step h) (step (h.mono (fun _ hw=>hw.symm)))

theorem discLocalAngularFraction_le_one (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) :
    discLocalAngularFraction S z≤1 := by
  apply (discLocalAngularFraction_le S z univ univ_mem).trans
  exact (measure_mono (subset_univ _)).trans_eq polygonDirectionMeasure_univ

/-- Interior points have the literal full angle even for nonconvex sets. -/
theorem discLocalAngularFraction_of_interior {S : Set Complex.UnitDisc} {z : Complex.UnitDisc}
    (hz : z∈interior S) : discLocalAngularFraction S z=1 := by
  apply le_antisymm (discLocalAngularFraction_le_one S z)
  apply le_iInf
  intro N
  apply le_of_eq
  symm
  apply discSubtendedAngularFraction_of_interior
  exact mem_interior_iff_mem_nhds.mpr
    (inter_mem (mem_interior_iff_mem_nhds.mp hz) N.property)

/-- Points outside the actual closure have zero germ angle, regardless of remote rays. -/
theorem discLocalAngularFraction_of_not_mem_closure {S : Set Complex.UnitDisc}
    {z : Complex.UnitDisc} (hz : z∉closure S) : discLocalAngularFraction S z=0 := by
  apply le_antisymm _ bot_le
  have hn : (closure S)ᶜ∈𝓝 z:=isClosed_closure.isOpen_compl.mem_nhds hz
  apply (discLocalAngularFraction_le S z _ hn).trans
  have he : S∩(closure S)ᶜ=∅:=by
    apply eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hw,hnw⟩
    exact hnw (subset_closure hw)
  simp [he,discSubtendedAngularFraction,discRadialDirections]

/-- Native convex regions recover the previously formalized geometric subtended angle. -/
theorem discLocalAngularFraction_eq_of_convex {S : Set Complex.UnitDisc}
    (hS : DiscHConvex S) {z : Complex.UnitDisc} (hz : z∈S) :
    discLocalAngularFraction S z=discSubtendedAngularFraction S z := by
  have he (N : {N : Set Complex.UnitDisc // N∈𝓝 z}) :
      discSubtendedAngularFraction (S∩N.val) z=discSubtendedAngularFraction S z := by
    unfold discSubtendedAngularFraction
    rw [image_inter (discOriginNormalizer z).injective]
    congr 1
    apply discRadialDirections_inter_nhds
    · exact hS.isometry_image (discOriginNormalizer_isometry z)
    · rw [←discOriginNormalizer_apply_self z]
      exact mem_image_of_mem _ hz
    · have hn:=(discOriginNormalizer z).isOpenMap.image_mem_nhds N.property
      rwa [discOriginNormalizer_apply_self] at hn
  change (⨅N : {N : Set Complex.UnitDisc // N∈𝓝 z},_) = _
  simp_rw [he]
  let : Nonempty {N : Set Complex.UnitDisc // N∈𝓝 z}:=⟨⟨univ,univ_mem⟩⟩
  exact iInf_const

/-- Native isometries preserve the true local angular germ, including nonconvex sets. -/
theorem discLocalAngularFraction_isometry (f : Complex.UnitDisc≃ₜComplex.UnitDisc)
    (hf : let :=discHyperbolicMetric; Isometry f) (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) :
    discLocalAngularFraction (f '' S) (f z)=discLocalAngularFraction S z := by
  apply le_antisymm
  · apply le_iInf
    intro N
    have hn : f '' N.val∈𝓝 (f z):=f.isOpenMap.image_mem_nhds N.property
    calc
      discLocalAngularFraction (f '' S) (f z)≤
          discSubtendedAngularFraction ((f '' S)∩(f '' N.val)) (f z):=
        discLocalAngularFraction_le _ _ _ hn
      _=discSubtendedAngularFraction (f '' (S∩N.val)) (f z):=by
        rw [image_inter f.injective]
      _=discSubtendedAngularFraction (S∩N.val) z:=discSubtendedAngularFraction_isometry f hf _ _
  · apply le_iInf
    intro N
    have hn : f ⁻¹' N.val∈𝓝 z:=f.continuous.continuousAt.preimage_mem_nhds N.property
    calc
      discLocalAngularFraction S z≤discSubtendedAngularFraction (S∩f ⁻¹' N.val) z:=
        discLocalAngularFraction_le _ _ _ hn
      _=discSubtendedAngularFraction (f '' (S∩f ⁻¹' N.val)) (f z):=
        (discSubtendedAngularFraction_isometry f hf _ _).symm
      _≤discSubtendedAngularFraction ((f '' S)∩N.val) (f z):=by
        apply discSubtendedAngularFraction_mono
        rintro w ⟨v,⟨hvS,hvN⟩,rfl⟩
        exact ⟨mem_image_of_mem f hvS,hvN⟩

theorem discLocalAngle_isometry (f : Complex.UnitDisc≃ₜComplex.UnitDisc)
    (hf : let :=discHyperbolicMetric; Isometry f) (S : Set Complex.UnitDisc) (z : Complex.UnitDisc) :
    discLocalAngle (f '' S) (f z)=discLocalAngle S z := by
  rw [discLocalAngle,discLocalAngle,discLocalAngularFraction_isometry f hf]

theorem discLocalAngle_of_interior {S : Set Complex.UnitDisc} {z : Complex.UnitDisc}
    (hz : z∈interior S) : discLocalAngle S z=2*Real.pi := by
  rw [discLocalAngle,discLocalAngularFraction_of_interior hz,ENNReal.toReal_one,mul_one]

theorem discLocalAngle_of_not_mem_closure {S : Set Complex.UnitDisc} {z : Complex.UnitDisc}
    (hz : z∉closure S) : discLocalAngle S z=0 := by
  rw [discLocalAngle,discLocalAngularFraction_of_not_mem_closure hz,ENNReal.toReal_zero,mul_zero]

theorem discLocalAngle_eq_of_convex {S : Set Complex.UnitDisc}
    (hS : DiscHConvex S) {z : Complex.UnitDisc} (hz : z∈S) :
    discLocalAngle S z=discSubtendedAngle S z := by
  rw [discLocalAngle,discSubtendedAngle,discLocalAngularFraction_eq_of_convex hS hz]

end LowDimensionalTopology.Geometry.Hyperbolic
