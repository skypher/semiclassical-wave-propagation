import Qschubert.LaplacianM
import Qschubert.Energy

/-!
# `-Δ` is nonnegative on periodized test functions

Spine stage S4 (`lean/BLUEPRINT.md`). For a Fuchsian `Γ` and a test function `F`,
`Re ⟪F_Γ, -(ΔF)_Γ⟫_{L²(M)} ≥ 0`. The pairing unfolds to `∫_ℍ y² ∇F · conj ∇U dν` with `U` the finite
sum of the translates of `F` meeting `supp F`; on `supp F`, `U` agrees with the lift `L` of `F_Γ`.
Folding back to `M` with the invariance of the energy density (`hgrad_comp_smul`) gives
`∫_M y² |∇L|² dμ ≥ 0` (`perioT_lap_nonneg`). Only the nonnegativity is packaged: the finiteness of the
quotient energy and the exact identity `⟪F_Γ, -(ΔF)_Γ⟫ = ∫_M y² |∇L|² dμ` are not stated here.

Contents: the lift `L` and its local finite-sum form; the unfolded pairing; the fold; positivity.
-/

namespace Qschubert

open MeasureTheory Complex Filter Topology
open scoped ComplexConjugate ContDiff MatrixGroups UpperHalfPlane Pointwise

lemma extC_eventuallyEq_of {A B : ℍ → ℂ} {z₀ : ℍ} (h : A =ᶠ[𝓝 z₀] B) :
    extC A =ᶠ[𝓝 (z₀ : ℂ)] extC B := by
  obtain ⟨t, ht, hAB⟩ := Filter.eventually_iff_exists_mem.1 h
  refine Filter.eventually_iff_exists_mem.2 ⟨(fun z : ℍ => (z : ℂ)) '' t,
    UpperHalfPlane.isOpenEmbedding_coe.image_mem_nhds.2 ht, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [extC, UpperHalfPlane.ofComplex_apply]
  exact hAB z hz

variable (Γ : Subgroup PGL(2, ℝ))

/-- The lift `z ↦ u_Γ(Γz)` of the periodization to `ℍ`. -/
noncomputable def liftP (u : ℍ → ℂ) : ℍ → ℂ := fun z => perio Γ u (surfMk Γ z)

lemma liftP_smul (u : ℍ → ℂ) (γ : Γ) (z : ℍ) : liftP Γ u (γ • z) = liftP Γ u z := by
  simp only [liftP, surfMk_smul]

variable [ProperlyDiscontinuousSMul Γ ℍ]

open Classical in
/-- If every translate outside a finite `S` vanishes near `z₀`, the lift is the sum over `S` near
`z₀`. -/
lemma liftP_eventuallyEq_sum {u : ℍ → ℂ} (hu : HasCompactSupport u) (z₀ : ℍ) (S : Finset Γ)
    (hS : ∀ γ ∉ S, ∀ᶠ z in 𝓝 z₀, u (γ • z) = 0) :
    ∀ᶠ z in 𝓝 z₀, liftP Γ u z = ∑ γ ∈ S, u (γ • z) := by
  obtain ⟨t, ht, hT⟩ := locallyFinite_support_smul Γ hu z₀
  have hev : ∀ᶠ z in 𝓝 z₀, ∀ γ ∈ hT.toFinset \ S, u (γ • z) = 0 :=
    (Filter.eventually_all_finset _).2 fun γ hγ => hS γ (Finset.mem_sdiff.1 hγ).2
  filter_upwards [ht, hev] with z hzt hz
  rw [liftP, perio_mk]
  refine tsum_eq_sum fun γ hγS => ?_
  by_cases hγT : γ ∈ hT.toFinset
  · exact hz γ (Finset.mem_sdiff.2 ⟨hγT, hγS⟩)
  · by_contra hne
    exact hγT ((Set.Finite.mem_toFinset _).2 ⟨z, hne, hzt⟩)

/-- Near every point, all but finitely many translates vanish, and the lift is their sum. -/
lemma exists_local_finset {u : ℍ → ℂ} (hu : HasCompactSupport u) (z₀ : ℍ) :
    ∃ T : Finset Γ, (∀ γ ∉ T, ∀ᶠ z in 𝓝 z₀, u (γ • z) = 0)
      ∧ ∀ᶠ z in 𝓝 z₀, liftP Γ u z = ∑ γ ∈ T, u (γ • z) := by
  obtain ⟨t, ht, hT⟩ := locallyFinite_support_smul Γ hu z₀
  have h1 : ∀ γ ∉ hT.toFinset, ∀ᶠ z in 𝓝 z₀, u (γ • z) = 0 := by
    intro γ hγ
    filter_upwards [ht] with z hz
    by_contra hne
    exact hγ ((Set.Finite.mem_toFinset _).2 ⟨z, hne, hz⟩)
  exact ⟨hT.toFinset, h1, liftP_eventuallyEq_sum Γ hu z₀ _ h1⟩

/-- The sum of the translates `F ∘ γ`, `γ ∈ T`, as a function on `ℂ`. -/
noncomputable def transSum (T : Finset Γ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun w => ∑ γ ∈ T, testComp (pglRep (γ : PGL(2, ℝ))) F w

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma isTestFn_transSum (T : Finset Γ) {F : ℂ → ℂ} (hF : IsTestFn F) : IsTestFn (transSum Γ T F) := by
  have : transSum Γ T F = ∑ γ ∈ T, testComp (pglRep (γ : PGL(2, ℝ))) F := by
    funext w; simp [transSum]
  rw [this]
  exact Submodule.sum_mem testFn fun γ _ => isTestFn_testComp hF _

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma tfn_smul (F : testFn) (γ : Γ) (z : ℍ) :
    tfn F (γ • z) = testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ) z := by
  rw [testComp_coe, pglRep_smul]; rfl

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma extC_liftP_eventuallyEq (F : testFn) (z₀ : ℍ) (T : Finset Γ)
    (hT : ∀ᶠ z in 𝓝 z₀, liftP Γ (tfn F) z = ∑ γ ∈ T, tfn F (γ • z)) :
    extC (liftP Γ (tfn F)) =ᶠ[𝓝 (z₀ : ℂ)] transSum Γ T F := by
  have hT' : liftP Γ (tfn F) =ᶠ[𝓝 z₀] fun z : ℍ => transSum Γ T F z := by
    filter_upwards [hT] with z hz
    rw [hz]
    simp only [transSum, tfn_smul]
  exact (extC_eventuallyEq_of hT').trans (extC_eventuallyEq (fun w => rfl) z₀)

/-- The lift of `F_Γ` is smooth on `ℍ`. -/
theorem contDiffAt_extC_liftP (F : testFn) (z₀ : ℍ) :
    ContDiffAt ℝ ∞ (extC (liftP Γ (tfn F))) (z₀ : ℂ) := by
  obtain ⟨T, _, hT⟩ := exists_local_finset Γ (hasCompactSupport_tfn F) z₀
  exact (isTestFn_transSum Γ T F.2).smooth.contDiffAt.congr_of_eventuallyEq
    (extC_liftP_eventuallyEq Γ F z₀ T hT)

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma gradPair_congr {f₁ f₂ k₁ k₂ : ℂ → ℂ} {w : ℂ} (hf : f₁ =ᶠ[𝓝 w] f₂) (hk : k₁ =ᶠ[𝓝 w] k₂) :
    gradPair f₁ k₁ w = gradPair f₂ k₂ w := by
  rw [gradPair, gradPair, hf.fderiv_eq, hk.fderiv_eq]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma gradPair_sum_left {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {k : ℂ → ℂ} {w : ℂ}
    (hf : ∀ i ∈ T, DifferentiableAt ℝ (f i) w) :
    gradPair (fun y => ∑ i ∈ T, f i y) k w = ∑ i ∈ T, gradPair (f i) k w := by
  rw [gradPair, fderiv_fun_sum hf]
  simp only [FunLike.coe_sum, Finset.sum_apply, Finset.sum_mul, gradPair,
    ← Finset.sum_add_distrib]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma gradPair_sum_right {ι : Type*} (T : Finset ι) {f : ℂ → ℂ} {k : ι → ℂ → ℂ} {w : ℂ}
    (hk : ∀ i ∈ T, DifferentiableAt ℝ (k i) w) :
    gradPair f (fun y => ∑ i ∈ T, k i y) w = ∑ i ∈ T, gradPair f (k i) w := by
  rw [gradPair, fderiv_fun_sum hk]
  simp only [FunLike.coe_sum, Finset.sum_apply, map_sum, Finset.mul_sum, gradPair,
    ← Finset.sum_add_distrib]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma gradPair_eq_zero_of_notMem {f k : ℂ → ℂ} {w : ℂ} (hw : w ∉ tsupport f) :
    gradPair f k w = 0 := by
  have : fderiv ℝ f w = 0 := Function.notMem_support.1 fun h => hw (support_fderiv_subset ℝ h)
  simp [gradPair, this]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma dirForm_eq_integral (F G : ℂ → ℂ) : dirForm F G = ∫ w, gradPair F G w := rfl

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma continuous_gradPair {F G : ℂ → ℂ} (hF : IsTestFn F) (hG : IsTestFn G) :
    Continuous (gradPair F G) := by
  have hcF : Continuous (fderiv ℝ F) := hF.smooth.continuous_fderiv (by simp)
  have hcG : Continuous (fderiv ℝ G) := hG.smooth.continuous_fderiv (by simp)
  unfold gradPair
  fun_prop

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma hasCompactSupport_gradPair {F G : ℂ → ℂ} (hF : IsTestFn F) :
    HasCompactSupport (gradPair F G) := by
  show HasCompactSupport (fun w => fderiv ℝ F w 1 * conj (fderiv ℝ G w 1)
    + fderiv ℝ F w I * conj (fderiv ℝ G w I))
  exact ((hF.compact.fderiv_apply (𝕜 := ℝ) 1).mul_right).add
    ((hF.compact.fderiv_apply (𝕜 := ℝ) I).mul_right)

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma integrable_gradPair {F G : ℂ → ℂ} (hF : IsTestFn F) (hG : IsTestFn G) :
    Integrable (gradPair F G) :=
  (continuous_gradPair hF hG).integrable_of_hasCompactSupport (hasCompactSupport_gradPair hF)

/-- `⟪F_Γ, (ΔF)_Γ⟫ = -Σ_{γ ∈ S} dirForm F (F ∘ γ)`, `S` the transporter of `supp F` into itself. -/
lemma inner_perioT_lap_eq (F : testFn) :
    inner ℂ (perioT Γ F) (perioT Γ (lapTest F))
      = -∑ γ ∈ (transp_finite Γ (isCompact_preimage_tsupport F)
          (isCompact_preimage_tsupport F)).toFinset,
          dirForm F (testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ)) := by
  have hK := isCompact_preimage_tsupport F
  rw [perioT, perioT, inner_perioL2, integral_conj_perio_mul Γ (continuous_tfn _)
    (hasCompactSupport_tfn _) (continuous_tfn _) hK hK (tsupport_tfn_lapTest_subset F)
    (tsupport_tfn_subset F), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have hG' := isTestFn_testComp F.2 (pglRep (γ : PGL(2, ℝ)))
  calc ∫ z, conj (tfn F (γ • z)) * tfn (lapTest F) z
      = ∫ z : ℍ, lapH (fun w : ℍ => (F : ℂ → ℂ) w) z
          * conj (testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ) z) := by
        congr 1; funext z; rw [tfn_smul, tfn_lapTest, mul_comm]
    _ = ∫ w : ℂ, lapE F w * conj (testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ) w) :=
        integral_lapH_mul F.2 hG'
    _ = -dirForm F (testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ)) := integral_lapE_mul F.2 hG'

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- `Σ_{γ ∈ S} dirForm F (F ∘ γ) = ∫ gradPair F (Σ_{γ ∈ S} F ∘ γ)`. -/
lemma sum_dirForm_eq (F : testFn) (S : Finset Γ) :
    ∑ γ ∈ S, dirForm F (testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ))
      = ∫ w, gradPair F (transSum Γ S F) w := by
  have hG : ∀ γ : Γ, IsTestFn (testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ)) :=
    fun γ => isTestFn_testComp F.2 _
  simp only [dirForm_eq_integral]
  rw [← integral_finsetSum _ (fun γ _ => integrable_gradPair F.2 (hG γ))]
  congr 1
  funext w
  rw [show transSum Γ S F = fun y => ∑ γ ∈ S, testComp (pglRep (γ : PGL(2, ℝ))) (F : ℂ → ℂ) y
    from rfl, gradPair_sum_right S (fun γ _ => (hG γ).smooth.differentiable (by simp) w)]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- On `ℍ`, the energy density of `F` against a test function `U` is `y² gradPair F U`. -/
lemma hgrad_tfn (F : testFn) (U : ℂ → ℂ) (z : ℍ) :
    hgrad (tfn F) (fun w : ℍ => U w) z = (z.im : ℂ) ^ 2 * gradPair F U z := by
  rw [hgrad, gradPair_congr (f₂ := (F : ℂ → ℂ)) (k₂ := U)
    (extC_eventuallyEq (F := tfn F) (G := (F : ℂ → ℂ)) (fun w => rfl) z)
    (extC_eventuallyEq (F := fun w : ℍ => U w) (G := U) (fun w => rfl) z)]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- `∫_ℂ gradPair F U = ∫_ℍ hgrad F U dν`. -/
lemma integral_gradPair_eq (F : testFn) (U : ℂ → ℂ) :
    ∫ w, gradPair F U w = ∫ z : ℍ, hgrad (tfn F) (fun w : ℍ => U w) z := by
  simp_rw [hgrad_tfn]
  rw [integral_im_sq_mul (gradPair F U)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm
  exact gradPair_eq_zero_of_notMem fun h => hw ⟨⟨w, F.2.inside h⟩, rfl⟩

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma hgrad_congr {A₁ A₂ B₁ B₂ : ℍ → ℂ} {w : ℍ} (hA : A₁ =ᶠ[𝓝 w] A₂) (hB : B₁ =ᶠ[𝓝 w] B₂) :
    hgrad A₁ B₁ w = hgrad A₂ B₂ w := by
  unfold hgrad
  rw [gradPair_congr (extC_eventuallyEq_of hA) (extC_eventuallyEq_of hB)]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma hgrad_zero_left (B : ℍ → ℂ) (w : ℍ) : hgrad (fun _ => 0) B w = 0 := by
  have : extC (fun _ : ℍ => (0 : ℂ)) = fun _ => 0 := rfl
  simp [hgrad, gradPair, this]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma hgrad_self_re_nonneg (L : ℍ → ℂ) (z : ℍ) : 0 ≤ (hgrad L L z).re := by
  unfold hgrad gradPair
  rw [Complex.mul_conj, Complex.mul_conj]
  have : ((z.im : ℂ) ^ 2 * ((Complex.normSq (fderiv ℝ (extC L) z 1) : ℂ)
      + (Complex.normSq (fderiv ℝ (extC L) z I) : ℂ))).re
      = z.im ^ 2 * (Complex.normSq (fderiv ℝ (extC L) z 1)
        + Complex.normSq (fderiv ℝ (extC L) z I)) := by
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  rw [this]
  exact mul_nonneg (sq_nonneg _) (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma differentiableAt_extC_tfn (F : testFn) (z : ℍ) :
    DifferentiableAt ℝ (extC (tfn F)) (z : ℂ) :=
  ((F.2.smooth.differentiable (by simp)) z).congr_of_eventuallyEq
    (extC_eventuallyEq (F := tfn F) (G := (F : ℂ → ℂ)) (fun w => rfl) z)

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma differentiableAt_extC_tfn_smul (F : testFn) (γ : Γ) (z : ℍ) :
    DifferentiableAt ℝ (extC fun w => tfn F (γ • w)) (z : ℂ) := by
  have hG := isTestFn_testComp F.2 (pglRep (γ : PGL(2, ℝ)))
  exact ((hG.smooth.differentiable (by simp)) z).congr_of_eventuallyEq
    (extC_eventuallyEq (fun w => tfn_smul Γ F γ w) z)

/-- The energy density of `F` against the transporter sum agrees with that against the lift. -/
lemma hgrad_transSum_eq (F : testFn) (w : ℍ) :
    hgrad (tfn F) (fun z : ℍ => transSum Γ (transp_finite Γ (isCompact_preimage_tsupport F)
      (isCompact_preimage_tsupport F)).toFinset F z) w = hgrad (tfn F) (liftP Γ (tfn F)) w := by
  set K := (fun z : ℍ => (z : ℂ)) ⁻¹' tsupport (F : ℂ → ℂ)
  by_cases hw : w ∈ K
  · refine hgrad_congr EventuallyEq.rfl ?_
    have hS : ∀ γ ∉ (transp_finite Γ (isCompact_preimage_tsupport F)
        (isCompact_preimage_tsupport F)).toFinset, ∀ᶠ z in 𝓝 w, tfn F (γ • z) = 0 := by
      intro γ hγ
      have hγw : ((γ • w : ℍ) : ℂ) ∉ tsupport (F : ℂ → ℂ) := by
        intro h
        apply hγ
        rw [Set.Finite.mem_toFinset]
        exact ⟨γ • w, ⟨w, hw, rfl⟩, h⟩
      have hc : Continuous fun z : ℍ => ((γ • z : ℍ) : ℂ) :=
        UpperHalfPlane.continuous_coe.comp (continuous_const_smul γ)
      filter_upwards [(hc.tendsto w).eventually ((isClosed_tsupport _).isOpen_compl.mem_nhds hγw)]
        with z hz
      exact image_eq_zero_of_notMem_tsupport (f := (F : ℂ → ℂ)) hz
    filter_upwards [liftP_eventuallyEq_sum Γ (hasCompactSupport_tfn F) w _ hS] with z hz
    rw [hz]
    simp only [transSum, tfn_smul]
  · have h0 : ∀ B : ℍ → ℂ, hgrad (tfn F) B w = 0 := by
      intro B
      unfold hgrad
      rw [gradPair_congr (extC_eventuallyEq (F := tfn F) (G := (F : ℂ → ℂ)) (fun w => rfl) w)
        EventuallyEq.rfl, gradPair_eq_zero_of_notMem hw, mul_zero]
    rw [h0, h0]

/-- Folding: `Σ_γ hgrad F L (γ z) = hgrad L L z`, `L` the lift of `F_Γ`. -/
lemma tsum_hgrad_smul (F : testFn) (z : ℍ) :
    ∑' γ : Γ, hgrad (tfn F) (liftP Γ (tfn F)) (γ • z) = hgrad (liftP Γ (tfn F)) (liftP Γ (tfn F)) z := by
  set L := liftP Γ (tfn F)
  have hstep : ∀ γ : Γ, hgrad (tfn F) L (γ • z) = hgrad (fun w => tfn F (γ • w)) L z := by
    intro γ
    have hrep : ∀ w : ℍ, pglRep (γ : PGL(2, ℝ)) • w = γ • w := fun w => pglRep_smul _ w
    have h := hgrad_comp_smul (pglRep (γ : PGL(2, ℝ))) (A := tfn F) (B := L) z
      (by rw [hrep]; exact differentiableAt_extC_tfn F (γ • z))
      (by rw [hrep]; exact (contDiffAt_extC_liftP Γ F (γ • z)).differentiableAt (by simp))
    simp only [hrep, L, liftP_smul] at h
    exact h.symm
  simp_rw [hstep]
  obtain ⟨T, h1, h2⟩ := exists_local_finset Γ (hasCompactSupport_tfn F) z
  rw [tsum_eq_sum (s := T) fun γ hγ => by
    rw [hgrad_congr (h1 γ hγ) EventuallyEq.rfl, hgrad_zero_left]]
  have hsum : hgrad (fun w => ∑ γ ∈ T, tfn F (γ • w)) L z = ∑ γ ∈ T, hgrad (fun w => tfn F (γ • w)) L z := by
    unfold hgrad
    rw [show extC (fun w => ∑ γ ∈ T, tfn F (γ • w)) = fun y => ∑ γ ∈ T, extC (fun w => tfn F (γ • w)) y
      from rfl, gradPair_sum_left T (fun γ _ => differentiableAt_extC_tfn_smul Γ F γ z),
      Finset.mul_sum]
  rw [← hsum]
  exact hgrad_congr (h2.mono fun w hw => hw.symm) EventuallyEq.rfl

/-- **Positivity**: `Re ⟪F_Γ, -(ΔF)_Γ⟫_{L²(M)} ≥ 0` for every test function `F`. -/
theorem perioT_lap_nonneg (F : testFn) :
    0 ≤ (inner ℂ (perioT Γ F) (-perioT Γ (lapTest F))).re := by
  have := countable_of_properlyDiscontinuous Γ
  have hFD := isFundamentalDomain_fdSet Γ
  set S := (transp_finite Γ (isCompact_preimage_tsupport F)
    (isCompact_preimage_tsupport F)).toFinset with hS
  set h : ℍ → ℂ := hgrad (tfn F) (fun z : ℍ => transSum Γ S F z) with hdef
  have hh : ∀ z, h z = (z.im : ℂ) ^ 2 * gradPair F (transSum Γ S F) z := fun z => hgrad_tfn F _ z
  have hcont : Continuous h := by
    have e : h = fun z : ℍ => ((z.im : ℂ)) ^ 2 * gradPair F (transSum Γ S F) z := funext hh
    rw [e]
    exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2).mul
      ((continuous_gradPair F.2 (isTestFn_transSum Γ S F.2)).comp UpperHalfPlane.continuous_coe)
  have hcs : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_preimage_tsupport F) fun z hz => ?_
    rw [hh, gradPair_eq_zero_of_notMem hz, mul_zero]
  have hint : Integrable h := hcont.integrable_of_hasCompactSupport hcs
  have hm : AEStronglyMeasurable (MulAction.automorphize h : Surf Γ → ℂ) (surfMeasure Γ) :=
    (measurable_perio Γ hcont hcs).aestronglyMeasurable
  have hpt : ∀ x : Surf Γ, 0 ≤ (MulAction.automorphize h x).re := by
    intro x
    induction x using Quotient.inductionOn with | _ z
    show 0 ≤ (∑' γ : Γ, h (γ • z)).re
    have e : ∀ γ : Γ, h (γ • z) = hgrad (tfn F) (liftP Γ (tfn F)) (γ • z) := fun γ => by
      rw [hdef, hS]; exact hgrad_transSum_eq Γ F (γ • z)
    simp_rw [e]
    rw [tsum_hgrad_smul]
    exact hgrad_self_re_nonneg _ z
  rw [inner_neg_right, inner_perioT_lap_eq, neg_neg, ← hS, sum_dirForm_eq, integral_gradPair_eq,
    ← hdef, integral_eq_integral_automorphize Γ hFD hint hm]
  by_cases hi : Integrable (MulAction.automorphize h : Surf Γ → ℂ) (surfMeasure Γ)
  · rw [← RCLike.re_to_complex, ← integral_re hi]
    exact integral_nonneg fun x => by simpa using hpt x
  · rw [integral_undef hi]
    simp

end Qschubert
