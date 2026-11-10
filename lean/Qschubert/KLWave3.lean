import Qschubert.KLCosRep

/-!
# Weighted bounds for the mollifier

For a bounded weight `W` as in `KLWave`: `‖W J_ε u‖ ≤ M ‖W u‖`, `‖W X J_ε u‖ ≤ (M/ε) ‖W u‖` (and `Y`), `‖W Δ J_ε u‖ ≤ (M/ε²) ‖W u‖`
and `|⟪y, h J_ε g⟫ - ⟪J_ε y, h g⟫| ≤ C ε ‖W y‖ ‖W g‖`, with constants independent of the bound on `W`.

`spec_superpose`: a superposition of bounded spectral multipliers against an integrable weight.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **Superposition of spectral multipliers.** -/
theorem spec_superpose {w : ℝ → ℝ} {f : ℝ → ℝ → ℂ} {F : ℝ → ℂ} {b : ℝ → ℝ}
    (hf : ∀ s, f s ∈ BddMeasurable ℝ) (hF : F ∈ BddMeasurable ℝ)
    (hjm : Measurable (Function.uncurry f)) (hw : Continuous w)
    (hb : ∀ s x, ‖f s x‖ ≤ b s) (hwb : Integrable fun s => |w s| * b s)
    (hrep : ∀ x, ∫ s, (w s : ℂ) * f s x = F x)
    (hc : Continuous fun s => specE.integral (f s)) :
    (Integrable fun s => (w s : ℂ) • specE.integral (f s)) ∧ ∫ s, (w s : ℂ) • specE.integral (f s) = specE.integral F := by
  have hbound : ∀ s, ‖specE.integral (f s)‖ ≤ b s := fun s =>
    (specE.norm_integral_le (hf s)).trans (ciSup_le fun x => hb s x)
  have hwc : Continuous fun s => (w s : ℂ) := Complex.continuous_ofReal.comp hw
  have hint : Integrable fun s => (w s : ℂ) • specE.integral (f s) := by
    refine hwb.mono' (hwc.smul hc).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg _)
  refine ⟨hint, ?_⟩
  apply ContinuousLinearMap.coe_injective
  refine (ext_inner_map _ _).1 fun u => ?_
  show ⟪(∫ s, (w s : ℂ) • specE.integral (f s)) u, u⟫_ℂ = ⟪specE.integral F u, u⟫_ℂ
  rw [← inner_conj_symm, ← inner_conj_symm (specE.integral F u) u]
  congr 1
  set ν := specE.assoc u with hν
  have e1 : (∫ s, (w s : ℂ) • specE.integral (f s)) u = ∫ s, (w s : ℂ) • specE.integral (f s) u :=
    ContinuousLinearMap.integral_apply hint u
  have hu : Integrable fun s => (w s : ℂ) • specE.integral (f s) u := hint.apply_continuousLinearMap u
  rw [e1, ← integral_inner hu u, specE.inner_integral hF u]
  have hprod : Integrable (Function.uncurry fun s x => (w s : ℂ) * f s x) ((volume : Measure ℝ).prod ν) := by
    refine (hwb.comp_fst ν).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hwc.measurable.comp measurable_fst).mul hjm).aestronglyMeasurable
    · simp only [Function.uncurry]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb _ _) (abs_nonneg _)
  have e2 : ∀ s, ⟪u, (w s : ℂ) • specE.integral (f s) u⟫_ℂ = ∫ x, (w s : ℂ) * f s x ∂ν := fun s => by
    rw [inner_smul_right, specE.inner_integral (hf s) u, integral_const_mul]
  simp_rw [e2]
  rw [integral_integral_swap (f := fun s x => (w s : ℂ) * f s x) hprod]
  exact integral_congr_ae (Eventually.of_forall fun x => hrep x)

lemma mul_mem_B {f g : ℝ → ℂ} (hf : f ∈ BddMeasurable ℝ) (hg : g ∈ BddMeasurable ℝ) : f * g ∈ BddMeasurable ℝ := by
  rw [mem_bddMeasurable] at hf hg ⊢
  obtain ⟨hf1, C1, h1⟩ := hf
  obtain ⟨hg1, C2, h2⟩ := hg
  refine ⟨hf1.mul hg1, C1 * C2, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (h1 x) (h2 x) (norm_nonneg _) ((norm_nonneg _).trans (h1 x))

/-- Norm of `A((∫ w T) u)`. -/
lemma norm_superpose_le {T : ℝ → L2H' →L[ℂ] L2H'} {w : ℝ → ℝ} (hint : Integrable fun s => (w s : ℂ) • T s)
    (A : L2H' →L[ℂ] L2H') (u : L2H') {g : ℝ → ℝ} (hg : Integrable g) (h : ∀ s, |w s| * ‖A (T s u)‖ ≤ g s) :
    ‖A ((∫ s, (w s : ℂ) • T s) u)‖ ≤ ∫ s, g s := by
  have hu : Integrable fun s => (w s : ℂ) • T s u := hint.apply_continuousLinearMap u
  have e : (∫ s, (w s : ℂ) • T s) u = ∫ s, (w s : ℂ) • T s u := ContinuousLinearMap.integral_apply hint u
  rw [e, ← ContinuousLinearMap.integral_comp_comm A hu]
  refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun s => ?_)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact h s

lemma measurable_sincS_uncurry : Measurable (Function.uncurry fun (s x : ℝ) => sincS s √x) := by
  unfold sincS
  simp only [Function.uncurry_def]
  exact measurable_fst.mul (Real.continuous_sinc.measurable.comp (measurable_fst.mul (Real.continuous_sqrt.measurable.comp measurable_snd)))

lemma chiC_abs (R s : ℝ) : (chiC R |s|).J = (chiC R s).J := by
  show specE.integral _ = specE.integral _
  congr 1; funext x
  simp only [Cutoff.g, chiC, cR]
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]

lemma sincS_neg (s l : ℝ) : sincS (-s) l = -sincS s l := by
  unfold sincS
  rw [show -s * l = -(s * l) by ring, Real.sinc_neg]
  ring

lemma chiD_neg_J (R s : ℝ) : (chiD R (-s)).J = -(chiD R s).J := by
  have e : (chiD R (-s)).g = (-1 : ℂ) • (chiD R s).g := by
    funext x
    simp [Cutoff.g, chiD, dR, sincS_neg]
  show specE.integral _ = _
  rw [e, specE.integral_smul _ (chiD R s).g_mem, neg_one_smul]
  rfl

lemma chiD_neg_JS (R s : ℝ) : (chiD R (-s)).JS = -(chiD R s).JS := by
  have e : (chiD R (-s)).gS = (-1 : ℂ) • (chiD R s).gS := by
    funext x
    simp [Cutoff.gS, chiD, dR, sincS_neg]
  show specE.integral _ = _
  rw [e, specE.integral_smul _ (chiD R s).gS_mem, neg_one_smul]
  rfl

lemma chiD_neg_Bx (R s : ℝ) (v : L2H') : (chiD R (-s)).Bx v = -(chiD R s).Bx v := by
  show formVec 1 (Or.inl rfl) (formLift (((chiD R (-s)).J + (chiD R (-s)).JS) v))
    = -formVec 1 (Or.inl rfl) (formLift (((chiD R s).J + (chiD R s).JS) v))
  rw [chiD_neg_J, chiD_neg_JS, ← neg_add, ContinuousLinearMap.neg_apply, map_neg, map_neg]

lemma chiD_neg_By (R s : ℝ) (v : L2H') : (chiD R (-s)).By v = -(chiD R s).By v := by
  show formVec Complex.I (Or.inr rfl) (formLift (((chiD R (-s)).J + (chiD R (-s)).JS) v))
    = -formVec Complex.I (Or.inr rfl) (formLift (((chiD R s).J + (chiD R s).JS) v))
  rw [chiD_neg_J, chiD_neg_JS, ← neg_add, ContinuousLinearMap.neg_apply, map_neg, map_neg]

section wave

variable {W : ℂ → ℝ} {C ρ : ℝ} (hW : WaveW W C ρ) (R : ℝ) (u : L2H') (s : ℝ)
include hW

theorem wave_C' : ‖mulCL hW.sb ((chiC R s).J u)‖ ≤ Real.exp (2 * ρ * |s|) * ‖mulCL hW.sb ((chiC R 0).J u)‖ := by
  rw [← chiC_abs]
  exact wave_C hW R u (abs_nonneg s)

theorem wave_Bx' : ‖mulCL hW.sb ((chiD R s).Bx u)‖ ≤ Real.exp (2 * ρ * |s|) * ‖mulCL hW.sb ((chiC R 0).J u)‖ := by
  rcases abs_cases s with ⟨h, h2⟩ | ⟨h, h2⟩
  · rw [h]; exact wave_Bx hW R u h2
  · have e : s = -|s| := by rw [h]; ring
    rw [e, chiD_neg_Bx, map_neg, norm_neg, abs_neg, abs_abs]
    exact wave_Bx hW R u (abs_nonneg s)

theorem wave_By' : ‖mulCL hW.sb ((chiD R s).By u)‖ ≤ Real.exp (2 * ρ * |s|) * ‖mulCL hW.sb ((chiC R 0).J u)‖ := by
  rcases abs_cases s with ⟨h, h2⟩ | ⟨h, h2⟩
  · rw [h]; exact wave_By hW R u h2
  · have e : s = -|s| := by rw [h]; ring
    rw [e, chiD_neg_By, map_neg, norm_neg, abs_neg, abs_abs]
    exact wave_By hW R u (abs_nonneg s)

end wave

lemma continuous_chiC_J (R : ℝ) : Continuous fun s => (chiC R s).J :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_C_J R s).continuousAt

lemma continuous_chiD_JJS (R : ℝ) : Continuous fun s => (chiD R s).J + (chiD R s).JS :=
  (continuous_iff_continuousAt.2 fun s => (hasDerivAt_D_J R s).continuousAt).add
    (continuous_iff_continuousAt.2 fun s => (hasDerivAt_D_JS R s).continuousAt)

lemma chiD_add_integral (R s : ℝ) : specE.integral ((chiD R s).g + (chiD R s).gS) = (chiD R s).J + (chiD R s).JS :=
  specE.integral_add (chiD R s).g_mem (chiD R s).gS_mem

lemma measurable_cR_uncurry (R : ℝ) : Measurable (Function.uncurry fun (s x : ℝ) => cR R s x) := by
  unfold cR
  simp only [Function.uncurry_def]
  exact (Real.measurable_cos.comp (measurable_fst.mul (Real.continuous_sqrt.measurable.comp measurable_snd))).mul
    ((measurable_cutR R).comp measurable_snd)

lemma measurable_dR_uncurry (R : ℝ) : Measurable (Function.uncurry fun (s x : ℝ) => dR R s x) := by
  unfold dR
  exact measurable_sincS_uncurry.mul ((measurable_cutR R).comp measurable_snd)

lemma cR_zero (R x : ℝ) : cR R 0 x = cutR R x := by simp [cR]

lemma cutR_eq_zero {R x : ℝ} (hx : x < 0) : cutR R x = 0 := by
  unfold cutR
  rw [Set.indicator_of_notMem]
  simp [hx]

lemma cutR_eq_zero' {R x : ℝ} (hx : R < x) : cutR R x = 0 := by
  unfold cutR
  rw [Set.indicator_of_notMem]
  simp [hx]

namespace MollProfile

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (R : ℝ)
include hε

/-- `J P_R = ∫ h_ε(s) cos(sΛ) P_R ds`. -/
theorem rep_J : (Integrable fun s => (P.hC ε s : ℂ) • (chiC R s).J)
    ∧ ∫ s, (P.hC ε s : ℂ) • (chiC R s).J = (P.cutoffEps hε).J * (chiC R 0).J := by
  have h := spec_superpose (w := P.hC ε) (f := fun s => (chiC R s).g) (F := (P.cutoffEps hε).g * (chiC R 0).g) (b := fun _ => 1)
    (fun s => (chiC R s).g_mem) (mul_mem_B (P.cutoffEps hε).g_mem (chiC R 0).g_mem)
    (Complex.measurable_ofReal.comp (measurable_cR_uncurry R)) (P.continuous_hC ε hε)
    (fun s x => by
      show ‖((cR R s x : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_cR_le R s x).trans (cutR_le_one R x))
    (by simpa using (P.hC_int hε 0).1)
    (fun x => by
      show ∫ s, (P.hC ε s : ℂ) * ((cR R s x : ℝ) : ℂ) = ((P.jEps ε √|x| : ℝ) : ℂ) * ((cR R 0 x : ℝ) : ℂ)
      simp_rw [← Complex.ofReal_mul]
      rw [integral_complex_ofReal]
      congr 1
      rcases lt_or_ge x 0 with hx | hx
      · simp [cR, cutR_eq_zero hx]
      · rw [abs_of_nonneg hx, P.jEps_eq_cos hε, cR_zero]
        simp only [cR, ← mul_assoc]
        exact integral_mul_const _ _)
    (continuous_chiC_J R)
  refine ⟨h.1, h.2.trans ?_⟩
  exact specE.integral_mul (P.cutoffEps hε).g_mem (chiC R 0).g_mem

include hε1

/-- `(J + JS) P_R = -∫ h_ε'(s) (D + DS) ds`. -/
theorem rep_JJS : (Integrable fun s => ((-P.hC1 ε s : ℝ) : ℂ) • ((chiD R s).J + (chiD R s).JS))
    ∧ ∫ s, ((-P.hC1 ε s : ℝ) : ℂ) • ((chiD R s).J + (chiD R s).JS)
      = ((P.cutoffEps hε).J + (P.cutoffEps hε).JS) * (chiC R 0).J := by
  have hF : ((P.cutoffEps hε).g + (P.cutoffEps hε).gS) ∈ BddMeasurable ℝ := (BddMeasurable ℝ).add_mem (P.cutoffEps hε).g_mem (P.cutoffEps hε).gS_mem
  have hfm : ∀ s, (chiD R s).g + (chiD R s).gS ∈ BddMeasurable ℝ := fun s => (BddMeasurable ℝ).add_mem (chiD R s).g_mem (chiD R s).gS_mem
  have hs1 : ∀ s : ℝ, |s| ≤ Real.exp (1 * |s|) := fun s => by
    have := Real.add_one_le_exp |s|
    rw [one_mul]; linarith
  have h := spec_superpose (w := fun s => -P.hC1 ε s) (f := fun s => (chiD R s).g + (chiD R s).gS)
    (F := ((P.cutoffEps hε).g + (P.cutoffEps hε).gS) * (chiC R 0).g) (b := fun s => (1 + |R|) * |s|)
    hfm (mul_mem_B hF (chiC R 0).g_mem)
    (by
      have e : Function.uncurry (fun s => (chiD R s).g + (chiD R s).gS)
          = fun p : ℝ × ℝ => ((dR R p.1 p.2 + p.2 * dR R p.1 p.2 : ℝ) : ℂ) := by
        funext p
        simp [Function.uncurry, Cutoff.g, Cutoff.gS, chiD]
      rw [e]
      exact Complex.measurable_ofReal.comp ((measurable_dR_uncurry R).add (measurable_snd.mul (measurable_dR_uncurry R))))
    (P.continuous_hC1 ε hε).neg
    (fun s x => by
      show ‖(((chiD R s).r x : ℝ) : ℂ) + ((x * (chiD R s).r x : ℝ) : ℂ)‖ ≤ _
      rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
      show |dR R s x + x * dR R s x| ≤ _
      rcases lt_or_ge x 0 with hx | hx
      · have : dR R s x = 0 := by simp [dR, cutR_eq_zero hx]
        rw [this]; simp; positivity
      rcases lt_or_ge R x with hR | hR
      · have : dR R s x = 0 := by simp [dR, cutR_eq_zero' hR]
        rw [this]; simp; positivity
      have h1 : |dR R s x| ≤ |s| := by
        refine (abs_dR_le R s x).trans ?_
        exact mul_le_of_le_one_right (abs_nonneg s) (cutR_le_one R x)
      have e : dR R s x + x * dR R s x = (1 + x) * dR R s x := by ring
      rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + x)]
      have hRa : x ≤ |R| := hR.trans (le_abs_self R)
      exact mul_le_mul (by linarith) h1 (abs_nonneg _) (by positivity))
    (by
      refine ((P.hC1_int hε hε1 1).1.const_mul (1 + |R|)).mono' ?_ (Eventually.of_forall fun s => ?_)
      · exact Continuous.aestronglyMeasurable (by have := (P.continuous_hC1 ε hε); fun_prop)
      · simp only [abs_neg]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := hs1 s
        have hR0 : 0 ≤ 1 + |R| := by positivity
        calc |P.hC1 ε s| * ((1 + |R|) * |s|) = (1 + |R|) * (|P.hC1 ε s| * |s|) := by ring
          _ ≤ (1 + |R|) * (|P.hC1 ε s| * Real.exp (1 * |s|)) := by gcongr)
    (fun x => by
      show ∫ s, ((-P.hC1 ε s : ℝ) : ℂ) * (((chiD R s).r x : ℝ) + ((x * (chiD R s).r x : ℝ) : ℂ))
        = (((P.jEps ε √|x| : ℝ) : ℂ) + ((x * P.jEps ε √|x| : ℝ) : ℂ)) * ((cR R 0 x : ℝ) : ℂ)
      simp_rw [← Complex.ofReal_add, ← Complex.ofReal_mul]
      rw [integral_complex_ofReal]
      congr 1
      rcases lt_or_ge x 0 with hx | hx
      · simp [chiD, dR, cR, cutR_eq_zero hx]
      · rw [abs_of_nonneg hx, cR_zero]
        have e : (fun s => -P.hC1 ε s * ((chiD R s).r x + x * (chiD R s).r x))
            = fun s => (-(1 + x) * cutR R x) * (P.hC1 ε s * sincS s √x) := by
          funext s
          show -P.hC1 ε s * (dR R s x + x * dR R s x) = _
          simp only [dR]
          ring
        rw [e, integral_const_mul, P.jEps_eq_sinc hε hε1]
        ring)
    (by
      have e : (fun s => specE.integral ((chiD R s).g + (chiD R s).gS)) = fun s => (chiD R s).J + (chiD R s).JS := by
        funext s; exact chiD_add_integral R s
      rw [e]
      exact continuous_chiD_JJS R)
  have e1 : ∀ s, specE.integral ((chiD R s).g + (chiD R s).gS) = (chiD R s).J + (chiD R s).JS := chiD_add_integral R
  simp_rw [e1] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [specE.integral_mul hF (chiC R 0).g_mem, specE.integral_add (P.cutoffEps hε).g_mem (P.cutoffEps hε).gS_mem]
  rfl

/-- `JS P_R = -∫ h_ε''(s) cos(sΛ) P_R ds`. -/
theorem rep_JS : (Integrable fun s => ((-P.hC2 ε s : ℝ) : ℂ) • (chiC R s).J)
    ∧ ∫ s, ((-P.hC2 ε s : ℝ) : ℂ) • (chiC R s).J = (P.cutoffEps hε).JS * (chiC R 0).J := by
  have h := spec_superpose (w := fun s => -P.hC2 ε s) (f := fun s => (chiC R s).g) (F := (P.cutoffEps hε).gS * (chiC R 0).g) (b := fun _ => 1)
    (fun s => (chiC R s).g_mem) (mul_mem_B (P.cutoffEps hε).gS_mem (chiC R 0).g_mem)
    (Complex.measurable_ofReal.comp (measurable_cR_uncurry R)) (P.continuous_hC2 ε hε).neg
    (fun s x => by
      show ‖((cR R s x : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_cR_le R s x).trans (cutR_le_one R x))
    (by simpa using (P.hC2_int hε hε1 0).1)
    (fun x => by
      show ∫ s, ((-P.hC2 ε s : ℝ) : ℂ) * ((cR R s x : ℝ) : ℂ) = ((x * P.jEps ε √|x| : ℝ) : ℂ) * ((cR R 0 x : ℝ) : ℂ)
      simp_rw [← Complex.ofReal_mul]
      rw [integral_complex_ofReal]
      congr 1
      rcases lt_or_ge x 0 with hx | hx
      · simp [cR, cutR_eq_zero hx]
      · rw [abs_of_nonneg hx, cR_zero]
        have h2 := P.jEps_eq_cos2 hε hε1 √x
        rw [Real.sq_sqrt hx] at h2
        rw [h2]
        have e : (fun s => -P.hC2 ε s * cR R s x) = fun s => (-cutR R x) * (P.hC2 ε s * Real.cos (s * √x)) := by
          funext s
          simp only [cR]
          ring
        rw [e, integral_const_mul]
        ring)
    (continuous_chiC_J R)
  refine ⟨h.1, h.2.trans ?_⟩
  exact specE.integral_mul (P.cutoffEps hε).gS_mem (chiC R 0).g_mem

end MollProfile

lemma tendsto_PR (u : L2H') : Tendsto (fun n : ℕ => (chiC n 0).J u) atTop (𝓝 u) := by
  have h := tendsto_chiC 0 u
  have hz : cosOp 0 = 1 := by
    have e : (fun x : ℝ => ((Real.cos (0 * √x) : ℝ) : ℂ)) = 1 := by funext x; simp
    rw [cosOp, e, specE.integral_one]
  rwa [hz] at h

namespace MollProfile

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
variable {W : ℂ → ℝ} {C ρ : ℝ} (hW : WaveW W C ρ) (u : L2H')
include hW hε

theorem w_J : ‖mulCL hW.sb ((P.cutoffEps hε).J u)‖ ≤ P.mG (2 * ρ) * ‖mulCL hW.sb u‖ := by
  have hlev : ∀ n : ℕ, ‖mulCL hW.sb ((P.cutoffEps hε).J ((chiC n 0).J u))‖ ≤ P.mG (2 * ρ) * ‖mulCL hW.sb ((chiC n 0).J u)‖ := fun n => by
    obtain ⟨h1, h2⟩ := P.rep_J hε n
    obtain ⟨i1, i2⟩ := P.hC_int hε (2 * ρ)
    have key := norm_superpose_le h1 (mulCL hW.sb) u (i1.mul_const ‖mulCL hW.sb ((chiC n 0).J u)‖) (fun s => by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (wave_C' hW n u s) (abs_nonneg _))
    rw [h2, integral_mul_const] at key
    exact key.trans (mul_le_mul_of_nonneg_right i2 (norm_nonneg _))
  have t1 := ((mulCL hW.sb).continuous.tendsto _).comp (((P.cutoffEps hε).J.continuous.tendsto _).comp (tendsto_PR u))
  have t2 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_PR u)
  exact le_of_tendsto_of_tendsto' t1.norm (t2.norm.const_mul _) hlev

include hε1

theorem w_JS : ‖mulCL hW.sb ((P.cutoffEps hε).JS u)‖ ≤ ε⁻¹ * ε⁻¹ * P.mG (2 * ρ) * ‖mulCL hW.sb u‖ := by
  have hlev : ∀ n : ℕ, ‖mulCL hW.sb ((P.cutoffEps hε).JS ((chiC n 0).J u))‖ ≤ ε⁻¹ * ε⁻¹ * P.mG (2 * ρ) * ‖mulCL hW.sb ((chiC n 0).J u)‖ := fun n => by
    obtain ⟨h1, h2⟩ := P.rep_JS hε hε1 n
    obtain ⟨i1, i2⟩ := P.hC2_int hε hε1 (2 * ρ)
    have key := norm_superpose_le h1 (mulCL hW.sb) u (i1.mul_const ‖mulCL hW.sb ((chiC n 0).J u)‖) (fun s => by
      rw [abs_neg, mul_assoc]
      exact mul_le_mul_of_nonneg_left (wave_C' hW n u s) (abs_nonneg _))
    rw [h2, integral_mul_const] at key
    exact key.trans (mul_le_mul_of_nonneg_right i2 (norm_nonneg _))
  have t1 := ((mulCL hW.sb).continuous.tendsto _).comp (((P.cutoffEps hε).JS.continuous.tendsto _).comp (tendsto_PR u))
  have t2 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_PR u)
  exact le_of_tendsto_of_tendsto' t1.norm (t2.norm.const_mul _) hlev

theorem w_Bx : ‖mulCL hW.sb ((P.cutoffEps hε).Bx u)‖ ≤ ε⁻¹ * P.mG (2 * ρ) * ‖mulCL hW.sb u‖ := by
  set A : L2H' →L[ℂ] L2H' := (mulCL hW.sb).comp ((formVec 1 (Or.inl rfl)).comp formLift) with hA
  have hlev : ∀ n : ℕ, ‖mulCL hW.sb ((P.cutoffEps hε).Bx ((chiC n 0).J u))‖ ≤ ε⁻¹ * P.mG (2 * ρ) * ‖mulCL hW.sb ((chiC n 0).J u)‖ := fun n => by
    obtain ⟨h1, h2⟩ := P.rep_JJS hε hε1 n
    obtain ⟨i1, i2⟩ := P.hC1_int hε hε1 (2 * ρ)
    have key := norm_superpose_le h1 A u (i1.mul_const ‖mulCL hW.sb ((chiC n 0).J u)‖) (fun s => by
      rw [abs_neg, mul_assoc]
      exact mul_le_mul_of_nonneg_left (wave_Bx' hW n u s) (abs_nonneg _))
    rw [h2, integral_mul_const] at key
    exact key.trans (mul_le_mul_of_nonneg_right i2 (norm_nonneg _))
  have hBc : Continuous (P.cutoffEps hε).Bx := ContinuousLinearMap.continuous _
  have t1 := ((mulCL hW.sb).continuous.tendsto _).comp ((hBc.tendsto _).comp (tendsto_PR u))
  have t2 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_PR u)
  exact le_of_tendsto_of_tendsto' t1.norm (t2.norm.const_mul _) hlev

theorem w_By : ‖mulCL hW.sb ((P.cutoffEps hε).By u)‖ ≤ ε⁻¹ * P.mG (2 * ρ) * ‖mulCL hW.sb u‖ := by
  set A : L2H' →L[ℂ] L2H' := (mulCL hW.sb).comp ((formVec Complex.I (Or.inr rfl)).comp formLift) with hA
  have hlev : ∀ n : ℕ, ‖mulCL hW.sb ((P.cutoffEps hε).By ((chiC n 0).J u))‖ ≤ ε⁻¹ * P.mG (2 * ρ) * ‖mulCL hW.sb ((chiC n 0).J u)‖ := fun n => by
    obtain ⟨h1, h2⟩ := P.rep_JJS hε hε1 n
    obtain ⟨i1, i2⟩ := P.hC1_int hε hε1 (2 * ρ)
    have key := norm_superpose_le h1 A u (i1.mul_const ‖mulCL hW.sb ((chiC n 0).J u)‖) (fun s => by
      rw [abs_neg, mul_assoc]
      exact mul_le_mul_of_nonneg_left (wave_By' hW n u s) (abs_nonneg _))
    rw [h2, integral_mul_const] at key
    exact key.trans (mul_le_mul_of_nonneg_right i2 (norm_nonneg _))
  have hBc : Continuous (P.cutoffEps hε).By := ContinuousLinearMap.continuous _
  have t1 := ((mulCL hW.sb).continuous.tendsto _).comp ((hBc.tendsto _).comp (tendsto_PR u))
  have t2 := ((mulCL hW.sb).continuous.tendsto _).comp (tendsto_PR u)
  exact le_of_tendsto_of_tendsto' t1.norm (t2.norm.const_mul _) hlev

end MollProfile

namespace MollProfile

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε)
variable {W : ℂ → ℝ} {C ρ K : ℝ} (hW : WaveW2 W C ρ K)
include hW hε

/-- **The commutator of the mollifier with `h = W²`.** -/
theorem w_comm (y g : L2H') :
    ‖⟪y, mulCL hW.adm.sb ((P.cutoffEps hε).J g)⟫_ℂ - ⟪(P.cutoffEps hε).J y, mulCL hW.adm.sb g⟫_ℂ‖
      ≤ ε * ((8 * ρ + 2 * K + 2 * ρ) * P.mG (4 * ρ)) * ‖mulCL hW.sb y‖ * ‖mulCL hW.sb g‖ := by
  have hρ : 0 ≤ ρ := hW.ρ0
  have hK : 0 ≤ K := hW.K0
  set m := mulCL hW.adm.sb with hm
  set J := (P.cutoffEps hε).J with hJ
  have hlev : ∀ n : ℕ, ‖⟪(chiC n 0).J y, m (J ((chiC n 0).J g))⟫_ℂ - ⟪J ((chiC n 0).J y), m ((chiC n 0).J g)⟫_ℂ‖
      ≤ ε * ((8 * ρ + 2 * K + 2 * ρ) * P.mG (4 * ρ)) * ‖mulCL hW.sb ((chiC n 0).J y)‖ * ‖mulCL hW.sb ((chiC n 0).J g)‖ := fun n => by
    obtain ⟨h1, h2⟩ := P.rep_J hε n
    obtain ⟨i1, i2⟩ := P.hC_s_int hε (4 * ρ)
    set A := ‖mulCL hW.sb ((chiC n 0).J y)‖ with hA
    set B := ‖mulCL hW.sb ((chiC n 0).J g)‖ with hB
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    set Py := (chiC n 0).J y with hPy
    set Pg := (chiC n 0).J g with hPg
    have ig : Integrable fun s => ((P.hC ε s : ℝ) : ℂ) • (chiC n s).J g := h1.apply_continuousLinearMap g
    have iy : Integrable fun s => ((P.hC ε s : ℝ) : ℂ) • (chiC n s).J y := h1.apply_continuousLinearMap y
    have eg : J Pg = ∫ s, ((P.hC ε s : ℝ) : ℂ) • (chiC n s).J g := by
      have := ContinuousLinearMap.integral_apply h1 g
      rw [h2] at this
      exact this
    have ey : J Py = ∫ s, ((P.hC ε s : ℝ) : ℂ) • (chiC n s).J y := by
      have := ContinuousLinearMap.integral_apply h1 y
      rw [h2] at this
      exact this
    have img : Integrable fun s => m (((P.hC ε s : ℝ) : ℂ) • (chiC n s).J g) := m.integrable_comp ig
    have t1 : ⟪Py, m (J Pg)⟫_ℂ = ∫ s, ((P.hC ε s : ℝ) : ℂ) * ⟪Py, m ((chiC n s).J g)⟫_ℂ := by
      rw [eg, ← ContinuousLinearMap.integral_comp_comm m ig, ← integral_inner img]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [map_smul, inner_smul_right]
    have t2 : ⟪J Py, m Pg⟫_ℂ = ∫ s, ((P.hC ε s : ℝ) : ℂ) * ⟪(chiC n s).J y, m Pg⟫_ℂ := by
      rw [ey, ← inner_conj_symm, ← integral_inner iy, ← integral_conj]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [inner_smul_right, map_mul, Complex.conj_ofReal, inner_conj_symm]
    have bd : ∀ s, ‖((P.hC ε s : ℝ) : ℂ) * ⟪Py, m ((chiC n s).J g)⟫_ℂ - ((P.hC ε s : ℝ) : ℂ) * ⟪(chiC n s).J y, m Pg⟫_ℂ‖
        ≤ (8 * ρ + 2 * K + 2 * ρ) * (|P.hC ε s| * (|s| * (1 + |s|)) * Real.exp (4 * ρ * |s|)) * (A * B) := fun s => by
      have c := comm_wave hW n (abs_nonneg s) y g
      rw [chiC_abs] at c
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hs := abs_nonneg s
      have hh := abs_nonneg (P.hC ε s)
      have hE := Real.exp_pos (4 * ρ * |s|)
      have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
      have hstep : |s| * (8 * ρ + (2 * K + 2 * ρ) * |s|) * Real.exp (4 * ρ * |s|) * A * B
          ≤ (8 * ρ + 2 * K + 2 * ρ) * (|s| * (1 + |s|)) * Real.exp (4 * ρ * |s|) * A * B := by
        have h3 : 8 * ρ + (2 * K + 2 * ρ) * |s| ≤ (8 * ρ + 2 * K + 2 * ρ) * (1 + |s|) := by nlinarith [mul_nonneg hρ hs]
        have h4 : |s| * (8 * ρ + (2 * K + 2 * ρ) * |s|) ≤ |s| * ((8 * ρ + 2 * K + 2 * ρ) * (1 + |s|)) :=
          mul_le_mul_of_nonneg_left h3 hs
        have h5 : |s| * (8 * ρ + (2 * K + 2 * ρ) * |s|) * Real.exp (4 * ρ * |s|) * (A * B)
            ≤ |s| * ((8 * ρ + 2 * K + 2 * ρ) * (1 + |s|)) * Real.exp (4 * ρ * |s|) * (A * B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hE.le) hAB
        nlinarith
      calc |P.hC ε s| * ‖⟪Py, m ((chiC n s).J g)⟫_ℂ - ⟪(chiC n s).J y, m Pg⟫_ℂ‖
          ≤ |P.hC ε s| * ((8 * ρ + 2 * K + 2 * ρ) * (|s| * (1 + |s|)) * Real.exp (4 * ρ * |s|) * A * B) :=
            mul_le_mul_of_nonneg_left (c.trans hstep) hh
        _ = _ := by ring
    have ihg : Integrable fun s => (8 * ρ + 2 * K + 2 * ρ) * (|P.hC ε s| * (|s| * (1 + |s|)) * Real.exp (4 * ρ * |s|)) * (A * B) :=
      (i1.const_mul _).mul_const _
    have i3 : Integrable fun s => ((P.hC ε s : ℝ) : ℂ) * ⟪Py, m ((chiC n s).J g)⟫_ℂ := by
      have := (img.const_inner (𝕜 := ℂ) Py)
      refine this.congr (Eventually.of_forall fun s => ?_)
      simp only [map_smul, inner_smul_right]
    have i4 : Integrable fun s => ((P.hC ε s : ℝ) : ℂ) * ⟪(chiC n s).J y, m Pg⟫_ℂ := by
      have := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (iy.const_inner (𝕜 := ℂ) (m Pg))
      refine this.congr (Eventually.of_forall fun s => ?_)
      simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, inner_smul_right, map_mul, Complex.conj_ofReal, inner_conj_symm]
    rw [t1, t2, ← integral_sub i3 i4]
    refine (norm_integral_le_of_norm_le ihg (Eventually.of_forall bd)).trans ?_
    rw [integral_mul_const, integral_const_mul]
    have hc0 : 0 ≤ 8 * ρ + 2 * K + 2 * ρ := by positivity
    have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
    calc (8 * ρ + 2 * K + 2 * ρ) * (∫ s, |P.hC ε s| * (|s| * (1 + |s|)) * Real.exp (4 * ρ * |s|)) * (A * B)
        ≤ (8 * ρ + 2 * K + 2 * ρ) * (ε * P.mG (4 * ρ)) * (A * B) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left i2 hc0) hAB
      _ = _ := by ring
  have ty := tendsto_PR y
  have tg := tendsto_PR g
  have t1 : Tendsto (fun n : ℕ => ⟪(chiC n 0).J y, m (J ((chiC n 0).J g))⟫_ℂ - ⟪J ((chiC n 0).J y), m ((chiC n 0).J g)⟫_ℂ) atTop
      (𝓝 (⟪y, m (J g)⟫_ℂ - ⟪J y, m g⟫_ℂ)) :=
    (ty.inner ((m.continuous.tendsto _).comp ((J.continuous.tendsto _).comp tg))).sub
      (((J.continuous.tendsto _).comp ty).inner ((m.continuous.tendsto _).comp tg))
  have t2 := (((mulCL hW.sb).continuous.tendsto _).comp ty).norm
  have t3 := (((mulCL hW.sb).continuous.tendsto _).comp tg).norm
  exact le_of_tendsto_of_tendsto' t1.norm ((t2.const_mul _).mul t3) hlev

end MollProfile

end Qschubert
