import Qschubert.TestFnDense
import Physicslib4.Spectral.Unbounded.Basic

/-!
# `Δ` on test functions as a linear map

Spine stage S2 (`lean/BLUEPRINT.md`). On a test function `F` the hyperbolic Laplacian of `F ∘ coe` is
`(y² Δ_E F) ∘ coe` (`lapH_eq_im_sq_lapE`), and `y² Δ_E F` is again a test function. This gives a
linear map `lapTest : testFn →ₗ[ℂ] testFn`.
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Complex Topology
open scoped ComplexConjugate ContDiff

/-- `y² Δ_E F`. -/
noncomputable def lapTestFun (F : ℂ → ℂ) : ℂ → ℂ := fun w => ((w.im : ℝ) : ℂ) ^ 2 * lapE F w

lemma contDiff_second_apply {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (v₀ v : ℂ) :
    ContDiff ℝ ∞ fun w => fderiv ℝ (fderiv ℝ F) w v v₀ := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) le_rfl
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ F)) := h1.fderiv_right (m := ∞) le_rfl
  exact (h2.clm_apply contDiff_const).clm_apply contDiff_const

lemma contDiff_lapE {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (lapE F) :=
  (contDiff_second_apply hF 1 1).add (contDiff_second_apply hF Complex.I Complex.I)

lemma tsupport_second_apply_subset (F : ℂ → ℂ) (v₀ v : ℂ) :
    tsupport (fun w => fderiv ℝ (fderiv ℝ F) w v v₀) ⊆ tsupport F := by
  have h1 : tsupport (fun w => fderiv ℝ (fderiv ℝ F) w v) ⊆ tsupport F :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := fderiv ℝ F) v).trans
      (tsupport_fderiv_subset (𝕜 := ℝ) (f := F))
  exact (tsupport_comp_subset (g := fun L : ℂ →L[ℝ] ℂ => L v₀) (by simp) _).trans h1

lemma tsupport_lapE_subset (F : ℂ → ℂ) : tsupport (lapE F) ⊆ tsupport F :=
  (tsupport_add _ _).trans (Set.union_subset (tsupport_second_apply_subset F 1 1)
    (tsupport_second_apply_subset F Complex.I Complex.I))

lemma isTestFn_lapTestFun {F : ℂ → ℂ} (hF : IsTestFn F) : IsTestFn (lapTestFun F) := by
  have hsub : tsupport (lapTestFun F) ⊆ tsupport F :=
    (tsupport_mul_subset_right (f := fun w : ℂ => ((w.im : ℝ) : ℂ) ^ 2)).trans (tsupport_lapE_subset F)
  refine ⟨?_, ?_, hsub.trans hF.inside⟩
  · have him : ContDiff ℝ ∞ fun w : ℂ => ((w.im : ℝ) : ℂ) := (ofRealCLM.comp imCLM).contDiff
    exact (him.pow 2).mul (contDiff_lapE hF.smooth)
  · exact IsCompact.of_isClosed_subset hF.compact (isClosed_tsupport _) hsub

lemma lapE_add {F G : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (w : ℂ) :
    lapE (F + G) w = lapE F w + lapE G w := by
  have hF1 : ∀ x, DifferentiableAt ℝ F x := fun x => (hF.differentiable (by simp)) x
  have hG1 : ∀ x, DifferentiableAt ℝ G x := fun x => (hG.differentiable (by simp)) x
  have hF2 : ∀ x, DifferentiableAt ℝ (fderiv ℝ F) x :=
    fun x => ((hF.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) x
  have hG2 : ∀ x, DifferentiableAt ℝ (fderiv ℝ G) x :=
    fun x => ((hG.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) x
  have e1 : fderiv ℝ (F + G) = fderiv ℝ F + fderiv ℝ G := by
    funext x; exact fderiv_add (hF1 x) (hG1 x)
  have e2 : fderiv ℝ (fderiv ℝ (F + G)) w = fderiv ℝ (fderiv ℝ F) w + fderiv ℝ (fderiv ℝ G) w := by
    rw [e1]; exact fderiv_add (hF2 w) (hG2 w)
  simp only [lapE, e2, ContinuousLinearMap.add_apply]
  ring

lemma lapE_smul {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (c : ℂ) (w : ℂ) :
    lapE (c • F) w = c * lapE F w := by
  have hF1 : ∀ x, DifferentiableAt ℝ F x := fun x => (hF.differentiable (by simp)) x
  have hF2 : ∀ x, DifferentiableAt ℝ (fderiv ℝ F) x :=
    fun x => ((hF.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) x
  have e1 : fderiv ℝ (c • F) = c • fderiv ℝ F := by
    funext x; exact fderiv_const_smul (hF1 x) c
  have e2 : fderiv ℝ (fderiv ℝ (c • F)) w = c • fderiv ℝ (fderiv ℝ F) w := by
    rw [e1]; exact fderiv_const_smul (hF2 w) c
  simp only [lapE, e2, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `F ↦ y² Δ_E F` as a linear map on test functions. -/
noncomputable def lapTest : testFn →ₗ[ℂ] testFn where
  toFun F := ⟨lapTestFun F, isTestFn_lapTestFun F.2⟩
  map_add' F G := by
    apply Subtype.ext; funext w
    show lapTestFun ((F : ℂ → ℂ) + G) w = lapTestFun F w + lapTestFun G w
    simp only [lapTestFun]
    rw [lapE_add F.2.smooth G.2.smooth]; ring
  map_smul' c F := by
    apply Subtype.ext; funext w
    show lapTestFun (c • (F : ℂ → ℂ)) w = c * lapTestFun F w
    simp only [lapTestFun]
    rw [lapE_smul F.2.smooth]; ring

/-- On `ℍ`, `lapTest` is the hyperbolic Laplacian. -/
lemma lapTest_coe (F : testFn) (z : ℍ) :
    ((lapTest F : testFn) : ℂ → ℂ) z = lapH (fun w : ℍ => (F : ℂ → ℂ) w) z := by
  rw [lapH_eq_im_sq_lapE (F.2.smooth.of_le (by simp))]
  rfl

/-- `⟪toL2 F, toL2 G⟫ = ∫ conj(F) G` over `(ℍ, dx dy / y²)`. -/
lemma inner_toL2 (F G : testFn) :
    inner ℂ (toL2 F) (toL2 G) = ∫ z : ℍ, conj ((F : ℂ → ℂ) z) * (G : ℂ → ℂ) z := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have hF : ⇑(toL2 F) =ᵐ[volume] fun z : ℍ => (F : ℂ → ℂ) z := MemLp.coeFn_toLp (memLp_comp_coe F.2)
  have hG : ⇑(toL2 G) =ᵐ[volume] fun z : ℍ => (G : ℂ → ℂ) z := MemLp.coeFn_toLp (memLp_comp_coe G.2)
  filter_upwards [hF, hG] with z h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

/-- The range of `toL2`, the domain of `-Δ`. -/
noncomputable def lapDomain : Submodule ℂ (Lp ℂ 2 (volume : Measure ℍ)) := LinearMap.range toL2

/-- Test functions are linearly equivalent to the domain. -/
noncomputable def toL2Equiv : testFn ≃ₗ[ℂ] lapDomain := LinearEquiv.ofInjective toL2 toL2_injective

/-- `-Δ` on the dense domain of test functions, as an unbounded operator on `L²(ℍ)`. -/
noncomputable def negLap : Lp ℂ 2 (volume : Measure ℍ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  ⟨lapDomain, -(toL2 ∘ₗ lapTest ∘ₗ toL2Equiv.symm.toLinearMap)⟩

lemma negLap_toL2Equiv (F : testFn) : negLap (toL2Equiv F) = -toL2 (lapTest F) := by
  show -(toL2 (lapTest (toL2Equiv.symm (toL2Equiv F)))) = _
  rw [LinearEquiv.symm_apply_apply]

lemma coe_toL2Equiv (F : testFn) : ((toL2Equiv F : lapDomain) : Lp ℂ 2 (volume : Measure ℍ)) = toL2 F :=
  rfl

theorem negLap_hasDenseDomain : Physicslib4.Spectral.Unbounded.HasDenseDomain negLap := by
  show Dense (Set.range toL2)
  exact denseRange_toL2

theorem negLap_isSymmetric : Physicslib4.Spectral.Unbounded.IsSymmetric negLap := by
  intro φ ψ
  obtain ⟨F, rfl⟩ := toL2Equiv.surjective φ
  obtain ⟨G, rfl⟩ := toL2Equiv.surjective ψ
  rw [negLap_toL2Equiv, negLap_toL2Equiv, coe_toL2Equiv, coe_toL2Equiv, inner_neg_right,
    inner_neg_left, inner_toL2, inner_toL2]
  congr 1
  have hsym := lapH_symmetric F.2 G.2
  simp_rw [← lapTest_coe] at hsym
  have h1 : ∫ z : ℍ, conj ((F : ℂ → ℂ) z) * ((lapTest G : testFn) : ℂ → ℂ) z
      = conj (∫ z : ℍ, ((F : ℂ → ℂ) z) * conj (((lapTest G : testFn) : ℂ → ℂ) z)) := by
    rw [← integral_conj]; congr 1; funext z; simp [mul_comm]
  have h2 : ∫ z : ℍ, conj (((lapTest F : testFn) : ℂ → ℂ) z) * (G : ℂ → ℂ) z
      = conj (∫ z : ℍ, ((lapTest F : testFn) : ℂ → ℂ) z * conj ((G : ℂ → ℂ) z)) := by
    rw [← integral_conj]; congr 1; funext z; simp [mul_comm]
  rw [h1, h2, hsym]

theorem negLap_nonneg (φ : negLap.domain) : 0 ≤ (inner ℂ (φ : Lp ℂ 2 (volume : Measure ℍ)) (negLap φ)).re := by
  obtain ⟨F, rfl⟩ := toL2Equiv.surjective φ
  rw [negLap_toL2Equiv, coe_toL2Equiv, inner_neg_right, inner_toL2]
  have hpos := lapH_neg_nonneg F.2
  simp_rw [← lapTest_coe] at hpos
  have hsym := lapH_symmetric F.2 F.2
  simp_rw [← lapTest_coe] at hsym
  have h1 : ∫ z : ℍ, conj ((F : ℂ → ℂ) z) * ((lapTest F : testFn) : ℂ → ℂ) z
      = conj (∫ z : ℍ, (F : ℂ → ℂ) z * conj (((lapTest F : testFn) : ℂ → ℂ) z)) := by
    rw [← integral_conj]; congr 1; funext z; simp [mul_comm]
  rw [h1, ← hsym, ← map_neg, Complex.conj_re]
  exact hpos

/-- `-Δ` on test functions is a densely defined positive operator in physicslib4's sense
(symmetric, `0 ≤ Re ⟪ψ, -Δψ⟫`): the input of the Friedrichs construction. -/
theorem negLap_isPositive : Physicslib4.Spectral.Unbounded.IsPositive negLap :=
  ⟨negLap_isSymmetric, negLap_nonneg⟩

end Qschubert
