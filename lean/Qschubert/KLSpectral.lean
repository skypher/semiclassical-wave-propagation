import Qschubert.KLDensity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The spectral measure of `-Δ` in the KL picture

`assoc_eq_map`: for `u ∈ L²(ℍ)`, the spectral distribution of `u` for `-Δ` (physicslib4's
`(spectralMeasure negLapH).assoc u`) is the image of `|klU u|² · muU` under `m(k, ν) = ν² + 1/4`.
Proof: both are finite measures on `ℝ`, and for `f ∈ C_c(ℝ, ℝ)`,
`∫ f d(assoc u) = ⟪u, f(-Δ)u⟫ = ⟪klU u, klU (f(-Δ)u)⟫ = ∫ f(m) |klU u|² dmuU` (`klU_functionalCalculus`);
regular measures agreeing on `C_c` are equal (`Measure.ext_of_integral_eq_on_compactlySupported`).

Consequences, for every measurable `f` (in particular the unbounded `e^{α√s}` of `e^{αΛ}`):
* `mem_domain_fc_iff`: `u ∈ Dom f(-Δ)` iff `f(m) · klU u ∈ L²(muU)`;
* `norm_fc_sq`: `‖f(-Δ)u‖² = ∫ |f(m)|² |klU u|² dmuU`.

Used by `lem:fc` (the bound for `e^{α''Λ}` with `α'' > 0`, an unbounded operator, read in the KL
picture where `Λ` is multiplication by `Λ(ν)`, dd_appendix.tex:100–102).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal

/-- The spectral variable of `-Δ` in the KL picture, `m(k, ν) = ν² + 1/4`. -/
noncomputable def mKL (p : ℝ × ℝ) : ℝ := p.2 ^ 2 + 1 / 4

lemma measurable_mKL : Measurable mKL := by unfold mKL; fun_prop

/-- The spectral measure of `-Δ`. -/
noncomputable abbrev specE : ProjectionValuedMeasure ℝ (Lp ℂ 2 (volume : Measure UpperHalfPlane)) :=
  spectralMeasure negLapH_isSelfAdjoint

/-- `|klU u|² · muU`. -/
noncomputable def rhoU (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) : Measure (ℝ × ℝ) :=
  muU.withDensity fun p => ‖(klU u : ℝ × ℝ → ℂ) p‖ₑ ^ 2

lemma measurable_enorm_sq_klU (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) :
    Measurable fun p => ‖(klU u : ℝ × ℝ → ℂ) p‖ₑ ^ 2 :=
  (Lp.stronglyMeasurable _).measurable.enorm.pow_const 2

lemma lintegral_enorm_sq_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : Lp ℂ 2 μ) :
    ∫⁻ p, ‖(g : α → ℂ) p‖ₑ ^ 2 ∂μ < ⊤ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have h2 := h.lintegral_lt_top
  convert h2 using 2
  funext p
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

instance (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) : IsFiniteMeasure (rhoU u) :=
  isFiniteMeasure_withDensity (lintegral_enorm_sq_lt_top (klU u)).ne

lemma integral_rhoU {g : ℝ × ℝ → ℝ} (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) :
    ∫ p, g p ∂(rhoU u) = ∫ p, ‖(klU u : ℝ × ℝ → ℂ) p‖ ^ 2 * g p ∂muU := by
  rw [rhoU, integral_withDensity_eq_integral_toReal_smul (measurable_enorm_sq_klU u)
    (Eventually.of_forall fun _ => ENNReal.pow_lt_top enorm_lt_top)]
  congr 1

/-- **The spectral distribution of `u` for `-Δ` in the KL picture.** -/
theorem assoc_eq_map (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) :
    specE.assoc u = Measure.map mKL (rhoU u) := by
  refine Measure.ext_of_integral_eq_on_compactlySupported (fun f => ?_)
  set F : ℝ → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp f.continuous
  have hFs : HasCompactSupport F := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hFB : F ∈ BddMeasurable ℝ := by
    obtain ⟨C, hC⟩ := hFc.bounded_above_of_compact_support hFs
    exact (mem_bddMeasurable).2 ⟨hFc.measurable, C, hC⟩
  have h1 := specE.inner_integral hFB u
  have h2 := klU_functionalCalculus hFc hFs.is_zero_at_infty u
  have h3 : inner ℂ u (specE.integral F u) = inner ℂ (klU u) (klU (specE.integral F u)) :=
    (klUi.inner_map_map u _).symm
  have h4 : inner ℂ (klU u) (klU (specE.integral F u))
      = ((∫ p, ‖(klU u : ℝ × ℝ → ℂ) p‖ ^ 2 * f (mKL p) ∂muU : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [h2] with p hp
    rw [hp, RCLike.inner_apply']
    simp only [F, mKL]
    apply Complex.ext <;> simp [Complex.sq_norm, Complex.normSq_apply] <;> ring
  have hL : ((∫ x, f x ∂(specE.assoc u) : ℝ) : ℂ) = ∫ x, F x ∂(specE.assoc u) := integral_complex_ofReal.symm
  rw [integral_map measurable_mKL.aemeasurable (map_continuous f).aestronglyMeasurable, integral_rhoU]
  exact_mod_cast hL.trans (h1.symm.trans (h3.trans h4))

lemma memLp_rhoU_iff {g : ℝ × ℝ → ℂ} (hg : AEStronglyMeasurable g muU)
    (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) :
    MemLp g 2 (rhoU u) ↔ MemLp (fun p => g p * (klU u : ℝ × ℝ → ℂ) p) 2 muU := by
  have hgr : AEStronglyMeasurable g (rhoU u) := hg.mono_ac (withDensity_absolutelyContinuous _ _)
  have hgm : AEStronglyMeasurable (fun p => g p * (klU u : ℝ × ℝ → ℂ) p) muU :=
    hg.mul (Lp.aestronglyMeasurable _)
  rw [memLp_two_iff_integrable_sq_norm hgr, memLp_two_iff_integrable_sq_norm hgm, rhoU,
    integrable_withDensity_iff_integrable_smul' (measurable_enorm_sq_klU u)
      (Eventually.of_forall fun _ => ENNReal.pow_lt_top enorm_lt_top)]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  simp only [ENNReal.toReal_pow, toReal_enorm, smul_eq_mul, norm_mul, mul_pow]; ring

/-- **Domain of `f(-Δ)` in the KL picture.** -/
theorem mem_domain_fc_iff {f : ℝ → ℂ} (hf : Measurable f) (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) :
    u ∈ (functionalCalculus negLapH_isSelfAdjoint f).domain
      ↔ MemLp (fun p => f (mKL p) * (klU u : ℝ × ℝ → ℂ) p) 2 muU := by
  rw [functionalCalculus_domain, mem_integralDomain, assoc_eq_map,
    memLp_map_measure_iff hf.aestronglyMeasurable measurable_mKL.aemeasurable]
  exact memLp_rhoU_iff (hf.comp measurable_mKL).aestronglyMeasurable u

/-- **Norm of `f(-Δ) u` in the KL picture.** -/
theorem norm_fc_sq {f : ℝ → ℂ} (hf : Measurable f) (u : (functionalCalculus negLapH_isSelfAdjoint f).domain) :
    ‖functionalCalculus negLapH_isSelfAdjoint f u‖ ^ 2
      = ∫ p, ‖f (mKL p)‖ ^ 2 * ‖(klU (u : Lp ℂ 2 (volume : Measure UpperHalfPlane)) : ℝ × ℝ → ℂ) p‖ ^ 2 ∂muU := by
  have h := norm_sq_pmapIntegral (spectralMeasure negLapH_isSelfAdjoint) hf u
  rw [show functionalCalculus negLapH_isSelfAdjoint f u = pmapIntegral (spectralMeasure negLapH_isSelfAdjoint) f u
    from rfl, h]
  change ∫ x, ‖f x‖ ^ 2 ∂(specE.assoc (u : Lp ℂ 2 (volume : Measure UpperHalfPlane))) = _
  rw [assoc_eq_map, integral_map measurable_mKL.aemeasurable
    (hf.norm.pow_const 2).aestronglyMeasurable, integral_rhoU]
  congr 1; funext p; ring

end Qschubert
