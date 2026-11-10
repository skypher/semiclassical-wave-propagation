import Qschubert.LaplacianSA

/-!
# `X` and `Y` on the form space of `-Δ`

`X = y∂ₓ` and `Y = y∂_y` map test functions to test functions (`vfTest 1`, `vfTest I`), and
`⟪XF, XG⟫ + ⟪YF, YG⟫ = ⟪F, -ΔG⟫` (`inner_vf_add`; both sides are the Dirichlet form). Hence `X`, `Y`
are bounded from the form domain of `-Δ` to `L²(ℍ)` and extend to its completion, the form space `Q`
of the Friedrichs construction (`formVec`), with
`⟪Xu, Xw⟫ + ⟪Yu, Yw⟫ = ⟪u, w⟫_Q - ⟪ιu, ιw⟫` (`inner_formVec_add`). For `f₁, f₂` in the domain of the
self-adjoint `-Δ` (`negLapH`), with lifts `ι*(f + (-Δ)f)` to `Q`:
`⟪X f₁, X f₂⟫ + ⟪Y f₁, Y f₂⟫ = ⟪f₁, -Δ f₂⟫` (`inner_formVec_lift_add`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

/-- `y ∂_v F` on `ℂ`: `v = 1` gives `X = y∂ₓ`, `v = i` gives `Y = y∂_y`. -/
noncomputable def vfFun (v : ℂ) (F : ℂ → ℂ) (w : ℂ) : ℂ := ((w.im : ℝ) : ℂ) * fderiv ℝ F w v

lemma isTestFn_vfFun (v : ℂ) {F : ℂ → ℂ} (hF : IsTestFn F) : IsTestFn (vfFun v F) := by
  have hsub : tsupport (vfFun v F) ⊆ tsupport F :=
    (tsupport_mul_subset_right (f := fun w : ℂ => ((w.im : ℝ) : ℂ))).trans
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) v)
  refine ⟨?_, IsCompact.of_isClosed_subset hF.compact (isClosed_tsupport _) hsub, hsub.trans hF.inside⟩
  have him : ContDiff ℝ ∞ fun w : ℂ => ((w.im : ℝ) : ℂ) := (Complex.ofRealCLM.comp Complex.imCLM).contDiff
  exact him.mul ((hF.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const)

/-- `F ↦ y ∂_v F` as a linear map on test functions. -/
noncomputable def vfTest (v : ℂ) : testFn →ₗ[ℂ] testFn where
  toFun F := ⟨vfFun v F, isTestFn_vfFun v F.2⟩
  map_add' F G := by
    apply Subtype.ext; funext w
    show vfFun v ((F : ℂ → ℂ) + G) w = vfFun v F w + vfFun v G w
    have hF : DifferentiableAt ℝ (F : ℂ → ℂ) w := (F.2.smooth.differentiable (by simp)) w
    have hG : DifferentiableAt ℝ (G : ℂ → ℂ) w := (G.2.smooth.differentiable (by simp)) w
    simp only [vfFun, fderiv_add hF hG, add_apply]
    ring
  map_smul' c F := by
    apply Subtype.ext; funext w
    show vfFun v (c • (F : ℂ → ℂ)) w = c * vfFun v F w
    have hF : DifferentiableAt ℝ (F : ℂ → ℂ) w := (F.2.smooth.differentiable (by simp)) w
    simp only [vfFun, fderiv_const_smul hF c, smul_apply, smul_eq_mul]
    ring

lemma vfTest_coe (v : ℂ) (F : testFn) (w : ℂ) :
    ((vfTest v F : testFn) : ℂ → ℂ) w = ((w.im : ℝ) : ℂ) * fderiv ℝ (F : ℂ → ℂ) w v := rfl

lemma fderiv_eq_zero_of_im_nonpos (F : testFn) {w : ℂ} (hw : ¬ 0 < w.im) (v : ℂ) :
    fderiv ℝ (F : ℂ → ℂ) w v = 0 := by
  have h : w ∉ tsupport (fderiv ℝ (F : ℂ → ℂ)) :=
    fun h => hw (F.2.inside (tsupport_fderiv_subset (𝕜 := ℝ) h))
  rw [image_eq_zero_of_notMem_tsupport h]
  rfl

/-- `⟪y∂_vF, y∂_vG⟫ = ∫_ℂ conj(∂_vF) ∂_vG`. -/
lemma inner_vf (v : ℂ) (F G : testFn) :
    inner ℂ (toL2 (vfTest v F)) (toL2 (vfTest v G))
      = ∫ w : ℂ, conj (fderiv ℝ (F : ℂ → ℂ) w v) * fderiv ℝ (G : ℂ → ℂ) w v := by
  rw [inner_toL2]
  have e : ∀ z : ℍ, conj (((vfTest v F : testFn) : ℂ → ℂ) z) * ((vfTest v G : testFn) : ℂ → ℂ) z
      = (z.im : ℂ) ^ 2 * (conj (fderiv ℝ (F : ℂ → ℂ) z v) * fderiv ℝ (G : ℂ → ℂ) z v) := by
    intro z
    rw [vfTest_coe, vfTest_coe, map_mul, Complex.conj_ofReal]
    simp only [UpperHalfPlane.coe_im]
    ring
  simp_rw [e]
  rw [integral_im_sq_mul (fun w => conj (fderiv ℝ (F : ℂ → ℂ) w v) * fderiv ℝ (G : ℂ → ℂ) w v)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
  have hw' : ¬ 0 < w.im := fun h => hw ⟨⟨w, h⟩, rfl⟩
  simp [fderiv_eq_zero_of_im_nonpos G hw' v]

lemma integrable_fderiv_mul (F G : testFn) (v : ℂ) :
    Integrable fun w : ℂ => conj (fderiv ℝ (F : ℂ → ℂ) w v) * fderiv ℝ (G : ℂ → ℂ) w v := by
  have hF1 : Continuous fun w => fderiv ℝ (F : ℂ → ℂ) w v :=
    (F.2.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hG1 : Continuous fun w => fderiv ℝ (G : ℂ → ℂ) w v :=
    (G.2.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport fun w => fderiv ℝ (G : ℂ → ℂ) w v := G.2.compact.fderiv_apply (𝕜 := ℝ) v
  exact ((Complex.continuous_conj.comp hF1).mul hG1).integrable_of_hasCompactSupport hcs.mul_left

/-- **`⟪XF, XG⟫ + ⟪YF, YG⟫ = ⟪F, -ΔG⟫`** on test functions. -/
theorem inner_vf_add (F G : testFn) :
    inner ℂ (toL2 (vfTest 1 F)) (toL2 (vfTest 1 G)) + inner ℂ (toL2 (vfTest Complex.I F)) (toL2 (vfTest Complex.I G))
      = inner ℂ (toL2 F) (-toL2 (lapTest G)) := by
  rw [inner_vf, inner_vf, ← integral_add (integrable_fderiv_mul F G 1) (integrable_fderiv_mul F G Complex.I),
    inner_neg_right, inner_toL2]
  have h := integral_lapH_mul G.2 F.2
  rw [integral_lapE_mul G.2 F.2] at h
  have e : ∫ z : ℍ, conj ((F : ℂ → ℂ) z) * ((lapTest G : testFn) : ℂ → ℂ) z
      = ∫ z : ℍ, lapH (fun w : ℍ => (G : ℂ → ℂ) w) z * conj ((F : ℂ → ℂ) z) := by
    congr 1; funext z; rw [lapTest_coe, mul_comm]
  rw [e, h, neg_neg, dirForm]
  congr 1; funext w; ring

/-! ### The form space of `-Δ` -/

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- `FormDom negLap → lapDomain`, the identity. -/
noncomputable def toDomLin : FormDom negLap →ₗ[ℂ] lapDomain where
  toFun := FormDom.toDom negLap
  map_add' := FormDom.toDom_add negLap
  map_smul' := FormDom.toDom_smul negLap

/-- `x ↦ y∂_v x` on the form domain of `-Δ` (the test functions). -/
noncomputable def vfDomLin (v : ℂ) : FormDom negLap →ₗ[ℂ] L2H :=
  toL2 ∘ₗ vfTest v ∘ₗ toL2Equiv.symm.toLinearMap ∘ₗ toDomLin

lemma formDom_val_eq (x : FormDom negLap) :
    FormDom.val negLap x = toL2 (toL2Equiv.symm (FormDom.toDom negLap x)) := by
  conv_lhs => rw [FormDom.val, ← toL2Equiv.apply_symm_apply (FormDom.toDom negLap x)]
  rfl

lemma formDom_app_eq (x : FormDom negLap) :
    FormDom.app negLap x = -toL2 (lapTest (toL2Equiv.symm (FormDom.toDom negLap x))) := by
  conv_lhs => rw [FormDom.app, ← toL2Equiv.apply_symm_apply (FormDom.toDom negLap x)]
  exact negLap_toL2Equiv _

lemma inner_vfDomLin_add (x y : FormDom negLap) :
    inner ℂ (vfDomLin 1 x) (vfDomLin 1 y) + inner ℂ (vfDomLin Complex.I x) (vfDomLin Complex.I y)
      = inner ℂ (FormDom.val negLap x) (FormDom.app negLap y) := by
  rw [formDom_val_eq, formDom_app_eq]
  exact inner_vf_add _ _

lemma norm_vfDomLin_le (v : ℂ) (hv : v = 1 ∨ v = Complex.I) (x : FormDom negLap) :
    ‖vfDomLin v x‖ ≤ ‖x‖ := by
  have h := inner_vfDomLin_add x x
  have hre := congrArg Complex.re h
  have e1 : ‖vfDomLin 1 x‖ ^ 2 = (inner ℂ (vfDomLin 1 x) (vfDomLin 1 x)).re := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  have e2 : ‖vfDomLin Complex.I x‖ ^ 2 = (inner ℂ (vfDomLin Complex.I x) (vfDomLin Complex.I x)).re := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  rw [Complex.add_re, ← e1, ← e2] at hre
  have hn := FormDom.norm_sq_eq negLap x
  have hval := sq_nonneg ‖FormDom.val negLap x‖
  have hsq : ‖vfDomLin v x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rcases hv with rfl | rfl
    · nlinarith [sq_nonneg ‖vfDomLin Complex.I x‖]
    · nlinarith [sq_nonneg ‖vfDomLin 1 x‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- `y∂_v` (`v = 1`: `X`; `v = i`: `Y`) on the form domain, of norm at most `1`. -/
noncomputable def vfDom (v : ℂ) (hv : v = 1 ∨ v = Complex.I) : FormDom negLap →L[ℂ] L2H :=
  LinearMap.mkContinuous (vfDomLin v) 1 (fun x => by simpa using norm_vfDomLin_le v hv x)

/-- `X`, `Y` on the form space `Q` of `-Δ`. -/
noncomputable def formVec (v : ℂ) (hv : v = 1 ∨ v = Complex.I) : FormSpace negLap →L[ℂ] L2H :=
  (vfDom v hv).extend (UniformSpace.Completion.toComplL : FormDom negLap →L[ℂ] FormSpace negLap)

lemma formVec_coe (v : ℂ) (hv : v = 1 ∨ v = Complex.I) (x : FormDom negLap) :
    formVec v hv (x : FormSpace negLap) = vfDomLin v x :=
  ContinuousLinearMap.extend_eq (vfDom v hv)
    (e := (UniformSpace.Completion.toComplL : FormDom negLap →L[ℂ] FormSpace negLap))
    UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _) x

/-- `⟪Xu, Xw⟫ + ⟪Yu, Yw⟫ = ⟪u, w⟫_Q - ⟪ιu, ιw⟫` on the form space. -/
theorem inner_formVec_add (u w : FormSpace negLap) :
    inner ℂ (formVec 1 (Or.inl rfl) u) (formVec 1 (Or.inl rfl) w)
        + inner ℂ (formVec Complex.I (Or.inr rfl) u) (formVec Complex.I (Or.inr rfl) w)
      = inner ℂ u w - inner ℂ (formIncl negLap u) (formIncl negLap w) := by
  refine UniformSpace.Completion.induction_on₂ u w ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact (((formVec 1 _).continuous.comp continuous_fst).inner ((formVec 1 _).continuous.comp continuous_snd)).add
        (((formVec Complex.I _).continuous.comp continuous_fst).inner
          ((formVec Complex.I _).continuous.comp continuous_snd))
    · exact (continuous_fst.inner continuous_snd).sub
        (((formIncl negLap).continuous.comp continuous_fst).inner ((formIncl negLap).continuous.comp continuous_snd))
  · intro x y
    rw [formVec_coe, formVec_coe, formVec_coe, formVec_coe, inner_vfDomLin_add,
      UniformSpace.Completion.inner_coe, FormDom.inner_eq, FormDom.formInner, formIncl_coe, formIncl_coe]
    ring

/-- The lift `ι* : L² → Q`. -/
noncomputable def formLift : L2H →L[ℂ] FormSpace negLap := ContinuousLinearMap.adjoint (formIncl negLap)

/-- For `f₁ = R g₁`, `f₂ = R g₂` in the domain of `negLapH` (`R = ιι*`):
`⟪X ι*g₁, X ι*g₂⟫ + ⟪Y ι*g₁, Y ι*g₂⟫ = ⟪g₁ - R g₁, R g₂⟫ = ⟪-Δ f₁, f₂⟫`. -/
theorem inner_formVec_lift_add (g₁ g₂ : L2H) :
    inner ℂ (formVec 1 (Or.inl rfl) (formLift g₁)) (formVec 1 (Or.inl rfl) (formLift g₂))
        + inner ℂ (formVec Complex.I (Or.inr rfl) (formLift g₁)) (formVec Complex.I (Or.inr rfl) (formLift g₂))
      = inner ℂ (g₁ - formRes negLap g₁) (formRes negLap g₂) := by
  rw [inner_formVec_add, inner_sub_left]
  have h1 : inner ℂ (formLift g₁) (formLift g₂) = inner ℂ g₁ (formRes negLap g₂) := by
    rw [formLift, ContinuousLinearMap.adjoint_inner_left]
    rfl
  rw [h1]
  rfl

end Qschubert
