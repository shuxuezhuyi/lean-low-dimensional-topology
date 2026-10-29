/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedLiftDeckActions
public import LowDimensionalTopology.Geometry.Teichmuller.PoincareKernelSeries
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralNormalizedMarkingActions

/-!
# The induced homomorphism on the actual projective Fuchsian groups

The original conjugated covering action descends through its actual real Mobius
image. No homomorphism into chosen special-linear representatives is asserted.
For an actual marked homeomorphism the projective map is an isomorphism onto
the same target group, and the original canonical QC lift supplies all data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane MatrixGroups OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller
open LiZhongQC Hyperbolic Mobius

private theorem native_action_eq_of_realSLMobius_eq {A B : SL(2, ℝ)}
    (h : realSLMobius A = realSLMobius B) (z : ℍ) : A • z = B • z := by
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  exact (realSLMobius_action A z).symm.trans
    ((congrArg (fun g : complexMobiusGroup => g.val (z : ℂ)) h).trans
      (realSLMobius_action B z))

private theorem projectiveImage_ker_le_conjugatedCoverAction_ker
    (Γ : Subgroup SL(2, ℝ)) (F : ℍ ≃ₜ ℍ) :
    (ProjectivePoincare.imageHom Γ).ker ≤ (conjugatedCoverAction Γ F).ker := by
  intro γ hγ
  have he : realSLMobius γ.val = realSLMobius 1 :=
    (congrArg Subtype.val (MonoidHom.mem_ker.mp hγ)).trans (map_one realSLMobius).symm
  apply MonoidHom.mem_ker.mpr
  exact ((conjugatedCoverAction_apply_eq_iff Γ F γ 1).mpr
    (native_action_eq_of_realSLMobius_eq he)).trans (map_one (conjugatedCoverAction Γ F))

/-- The literal conjugated action factors through the entire actual projective source. -/
def projectiveConjugatedCoverAction (Γ : Subgroup SL(2, ℝ)) (F : ℍ ≃ₜ ℍ) :
    Γ.map realSLMobius →* (ℍ ≃ₜ ℍ) :=
  (ProjectivePoincare.imageHom Γ).liftOfSurjective
    (ProjectivePoincare.imageHom_surjective Γ)
    ⟨conjugatedCoverAction Γ F, by
      exact projectiveImage_ker_le_conjugatedCoverAction_ker Γ F⟩

theorem projectiveConjugatedCoverAction_image (Γ : Subgroup SL(2, ℝ))
    (F : ℍ ≃ₜ ℍ) (γ : Γ) :
    projectiveConjugatedCoverAction Γ F (ProjectivePoincare.imageHom Γ γ) =
      conjugatedCoverAction Γ F γ := by
  simp only [projectiveConjugatedCoverAction, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply]

/-- Faithfulness holds on actual transformations, rather than on signed matrices. -/
theorem projectiveConjugatedCoverAction_injective (Γ : Subgroup SL(2, ℝ))
    (F : ℍ ≃ₜ ℍ) : Function.Injective (projectiveConjugatedCoverAction Γ F) := by
  intro a b hab
  obtain ⟨γ, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ a
  obtain ⟨δ, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ b
  rw [projectiveConjugatedCoverAction_image, projectiveConjugatedCoverAction_image] at hab
  apply Subtype.ext
  exact realSLMobius_eq_of_native_action γ.val δ.val
    ((conjugatedCoverAction_apply_eq_iff Γ F γ δ).mp hab)

/-- The projective native action retains its original full sphere values on H. -/
theorem projectiveConjugatedCoverAction_id_sphere (Γ : Subgroup SL(2, ℝ))
    (g : Γ.map realSLMobius) (z : ℍ) :
    g.val.val (z : ℂ) =
      (((projectiveConjugatedCoverAction Γ (Homeomorph.refl ℍ) g z : ℍ) : ℂ) : ExtendedComplex) := by
  obtain ⟨γ, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
  rw [projectiveConjugatedCoverAction_image]
  exact realSLMobius_action γ.val z

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  {Γ Δ : Subgroup SL(2, ℝ)} {p : ℍ → X} {q : ℍ → Y}
  {f : X ≃ₜ Y} {F : ℍ ≃ₜ ℍ}

private theorem projectiveConjugatedCoverAction_mem_target_range
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q) (hF : IsLift p q f F)
    (g : Γ.map realSLMobius) : projectiveConjugatedCoverAction Γ F g ∈
      (projectiveConjugatedCoverAction Δ (Homeomorph.refl ℍ)).range := by
  obtain ⟨γ, rfl⟩ := ProjectivePoincare.imageHom_surjective Γ g
  obtain ⟨δ, hδ, he⟩ := conjugatedCoverAction_eq_deck hp hq hF γ
  refine ⟨ProjectivePoincare.imageHom Δ ⟨δ, hδ⟩, ?_⟩
  rw [projectiveConjugatedCoverAction_image, projectiveConjugatedCoverAction_image]
  apply Homeomorph.ext
  intro z
  exact (congrArg (fun H : ℍ ≃ₜ ℍ => H z) he).symm

/-- The induced homomorphism has the actual projective source and target deck groups. -/
def inducedProjectiveFuchsianHom
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q) (hF : IsLift p q f F) :
    Γ.map realSLMobius →* Δ.map realSLMobius :=
  (MonoidHom.ofInjective
    (projectiveConjugatedCoverAction_injective Δ (Homeomorph.refl ℍ))).symm.toMonoidHom.comp
      ((projectiveConjugatedCoverAction Γ F).codRestrict _
        (by exact projectiveConjugatedCoverAction_mem_target_range hp hq hF))

theorem inducedProjectiveFuchsianHom_action
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q) (hF : IsLift p q f F)
    (g : Γ.map realSLMobius) :
    projectiveConjugatedCoverAction Δ (Homeomorph.refl ℍ)
        (inducedProjectiveFuchsianHom hp hq hF g) = projectiveConjugatedCoverAction Γ F g := by
  exact MonoidHom.apply_ofInjective_symm
    (projectiveConjugatedCoverAction_injective Δ (Homeomorph.refl ℍ))
    ⟨_, projectiveConjugatedCoverAction_mem_target_range hp hq hF g⟩

/-- Every original matrix representative gives the same literal conjugation formula. -/
theorem inducedProjectiveFuchsianHom_image_apply
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q) (hF : IsLift p q f F)
    (γ : Γ) (z : ℍ) :
    (inducedProjectiveFuchsianHom hp hq hF (ProjectivePoincare.imageHom Γ γ)).val.val (z : ℂ) =
      (((F (γ.val • F.symm z) : ℍ) : ℂ) : ExtendedComplex) := by
  rw [projectiveConjugatedCoverAction_id_sphere, inducedProjectiveFuchsianHom_action,
    projectiveConjugatedCoverAction_image]
  rfl

theorem inducedProjectiveFuchsianHom_injective
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q) (hF : IsLift p q f F) :
    Function.Injective (inducedProjectiveFuchsianHom hp hq hF) := by
  intro a b hab
  apply projectiveConjugatedCoverAction_injective Γ F
  rw [← inducedProjectiveFuchsianHom_action hp hq hF a,
    ← inducedProjectiveFuchsianHom_action hp hq hF b, hab]

/-- The inverse original lift covers every actual target deck transformation. -/
theorem inducedProjectiveFuchsianHom_surjective
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q) (hF : IsLift p q f F) :
    Function.Surjective (inducedProjectiveFuchsianHom hp hq hF) := by
  intro d
  obtain ⟨δ, rfl⟩ := ProjectivePoincare.imageHom_surjective Δ d
  obtain ⟨γ, hγ, he⟩ := conjugatedCoverAction_eq_deck hq hp (s27g_isLift_symm hF) δ
  refine ⟨ProjectivePoincare.imageHom Γ ⟨γ, hγ⟩, ?_⟩
  apply projectiveConjugatedCoverAction_injective Δ (Homeomorph.refl ℍ)
  rw [inducedProjectiveFuchsianHom_action, projectiveConjugatedCoverAction_image,
    projectiveConjugatedCoverAction_image]
  apply Homeomorph.ext
  intro z
  have hz := congrArg (fun H : ℍ ≃ₜ ℍ => F (H (F.symm z))) he
  change F (F.symm (δ.val • F (F.symm z))) = F (γ • F.symm z) at hz
  change F (γ • F.symm z) = δ.val • z
  simpa only [F.apply_symm_apply] using hz.symm

/-- The marked lift induces an isomorphism onto the same actual target projective group. -/
def inducedProjectiveFuchsianEquiv
    (hp : IsUniformization Γ p) (hq : IsUniformization Δ q) (hF : IsLift p q f F) :
    Γ.map realSLMobius ≃* Δ.map realSLMobius :=
  MulEquiv.ofBijective (inducedProjectiveFuchsianHom hp hq hF)
    ⟨inducedProjectiveFuchsianHom_injective hp hq hF,
      inducedProjectiveFuchsianHom_surjective hp hq hF⟩

/-- Every original QC marking supplies its own actual canonical lift and target group. -/
def GeneralQC.canonicalInducedProjectiveFuchsianEquiv
    (R : GeneralQC.Surface.{u}) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → R.carrier}
    (hp : IsUniformization Γ p) (m : GeneralQC.Marked.{u, v} R) :
    Γ.map realSLMobius ≃*
      (s27u_conjGroup Γ (GeneralQC.canonicalMarkingLiftGeneral R hp m)).map realSLMobius :=
  inducedProjectiveFuchsianEquiv hp
    (GeneralQC.canonicalMarkingLiftGeneral_spec R hp m).2.1
    (GeneralQC.canonicalMarkingLiftGeneral_spec R hp m).2.2.1

/-- The canonical map has the book's formula for the same marking and every representative. -/
theorem GeneralQC.canonicalInducedProjectiveFuchsianEquiv_image_apply
    (R : GeneralQC.Surface.{u}) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → R.carrier}
    (hp : IsUniformization Γ p) (m : GeneralQC.Marked.{u, v} R) (γ : Γ) (z : ℍ) :
    (GeneralQC.canonicalInducedProjectiveFuchsianEquiv R hp m
        (ProjectivePoincare.imageHom Γ γ)).val.val (z : ℂ) =
      (((GeneralQC.canonicalMarkingLiftGeneral R hp m
        (γ.val • (GeneralQC.canonicalMarkingLiftGeneral R hp m).symm z) : ℍ) : ℂ) :
          ExtendedComplex) :=
  inducedProjectiveFuchsianHom_image_apply hp
    (GeneralQC.canonicalMarkingLiftGeneral_spec R hp m).2.1
    (GeneralQC.canonicalMarkingLiftGeneral_spec R hp m).2.2.1 γ z

/-- Its same original target covering supplies a genuine Fuchsian target group. -/
theorem GeneralQC.canonicalInducedProjectiveFuchsian_target_isFuchsian
    (R : GeneralQC.Surface.{u}) {Γ : Subgroup SL(2, ℝ)} {p : ℍ → R.carrier}
    (hp : IsUniformization Γ p) (m : GeneralQC.Marked.{u, v} R) :
    IsFuchsian (s27u_conjGroup Γ (GeneralQC.canonicalMarkingLiftGeneral R hp m)) :=
  utm_x2_isFuchsian (GeneralQC.canonicalMarkingLiftGeneral_spec R hp m).2.1

end LowDimensionalTopology.Geometry.Teichmuller
