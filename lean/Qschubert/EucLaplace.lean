import Qschubert.EucTransfer
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Cutoffs at `i`, real test functions, conjugation

The real cutoffs `χ` (`chiT`, `1` on `B(i, 1/4)`, support `B(i, 1/2)`) and `θ` (`thetaT`, `1` on
`B(i, 5/8)`, support `B(i, 3/4)`) are test functions, and `θ = 1` on a neighbourhood of
`tsupport χ` (`thetaT_eventuallyEq_one`). Real test functions are closed under `X`, `Y`, `Δ` and
division by `y` (`IsRealT`), and conjugation commutes with `X`, `Y`, `Δ` (`vfTest_conjT`,
`lapTest_conjT`). Mathlib's Laplacian on `ℂ` is `lapE` (`laplacian_eq_lapE`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Metric
open scoped ContDiff ComplexConjugate InnerProductSpace Laplacian

lemma im_pos_of_dist_lt_one {ζ : ℂ} (h : dist ζ Complex.I < 1) : 0 < ζ.im := by
  have h1 : |ζ.im - 1| ≤ dist ζ Complex.I := by
    rw [Complex.dist_eq]
    have := Complex.abs_im_le_norm (ζ - Complex.I)
    simpa using this
  have := abs_le.1 (h1.trans h.le)
  linarith [abs_le.1 h1]

lemma isTestFn_bump (b : ContDiffBump Complex.I) (hb : b.rOut < 1) :
    IsTestFn (fun ζ : ℂ => ((b ζ : ℝ) : ℂ)) := by
  have hsub : tsupport (fun ζ : ℂ => ((b ζ : ℝ) : ℂ)) ⊆ tsupport b :=
    tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero _
  refine ⟨Complex.ofRealCLM.contDiff.comp b.contDiff, b.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
  intro ζ hζ
  have h2 := hsub hζ
  rw [b.tsupport_eq, mem_closedBall] at h2
  exact im_pos_of_dist_lt_one (h2.trans_lt hb)

/-- The bump `1` on `B(i, 1/4)`, support `B(i, 1/2)`. -/
noncomputable def chiB : ContDiffBump Complex.I := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The bump `1` on `B(i, 5/8)`, support `B(i, 3/4)`. -/
noncomputable def thetaB : ContDiffBump Complex.I := ⟨5 / 8, 3 / 4, by norm_num, by norm_num⟩

noncomputable def chiT : testFn := ⟨_, isTestFn_bump chiB (by norm_num [chiB])⟩
noncomputable def thetaT : testFn := ⟨_, isTestFn_bump thetaB (by norm_num [thetaB])⟩

lemma chiT_apply (ζ : ℂ) : (chiT : ℂ → ℂ) ζ = ((chiB ζ : ℝ) : ℂ) := rfl

lemma chiT_eq_one {ζ : ℂ} (h : dist ζ Complex.I ≤ 1 / 4) : (chiT : ℂ → ℂ) ζ = 1 := by
  rw [chiT_apply, chiB.one_of_mem_closedBall (by rw [mem_closedBall]; exact h)]; simp

lemma thetaT_eventuallyEq_one {ζ : ℂ} (hζ : ζ ∈ tsupport (chiT : ℂ → ℂ)) :
    (thetaT : ℂ → ℂ) =ᶠ[𝓝 ζ] fun _ => 1 := by
  have hsub : tsupport (chiT : ℂ → ℂ) ⊆ tsupport chiB :=
    tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero _
  have h2 := hsub hζ
  rw [chiB.tsupport_eq, mem_closedBall] at h2
  have hball : ζ ∈ ball Complex.I thetaB.rIn := by
    rw [mem_ball]; exact h2.trans_lt (by norm_num [chiB, thetaB])
  filter_upwards [thetaB.eventuallyEq_one_of_mem_ball hball] with w hw
  show ((thetaB w : ℝ) : ℂ) = 1
  rw [hw]; simp

/-! ### Real test functions -/

/-- A real-valued test function. -/
def IsRealT (c : testFn) : Prop := ∀ ζ, conj ((c : ℂ → ℂ) ζ) = (c : ℂ → ℂ) ζ

lemma isRealT_chiT : IsRealT chiT := fun ζ => by rw [chiT_apply, Complex.conj_ofReal]

lemma fderiv_real_conj {c : testFn} (hc : IsRealT c) (w v : ℂ) :
    conj (fderiv ℝ (c : ℂ → ℂ) w v) = fderiv ℝ (c : ℂ → ℂ) w v := by
  have h := fderiv_conj_apply ((c.2.smooth.differentiable (by simp)) w) v
  have e : (fun x => conj ((c : ℂ → ℂ) x)) = (c : ℂ → ℂ) := funext hc
  rw [e] at h
  exact h.symm

lemma isRealT_vfTest (v : ℂ) {c : testFn} (hc : IsRealT c) : IsRealT (vfTest v c) := fun ζ => by
  rw [vfTest_coe, map_mul, Complex.conj_ofReal, fderiv_real_conj hc]

lemma isRealT_add {a b : testFn} (ha : IsRealT a) (hb : IsRealT b) : IsRealT (a + b) := fun ζ => by
  show conj ((a : ℂ → ℂ) ζ + (b : ℂ → ℂ) ζ) = (a : ℂ → ℂ) ζ + (b : ℂ → ℂ) ζ
  rw [map_add, ha, hb]

lemma isRealT_sub {a b : testFn} (ha : IsRealT a) (hb : IsRealT b) : IsRealT (a - b) := fun ζ => by
  show conj ((a : ℂ → ℂ) ζ - (b : ℂ → ℂ) ζ) = (a : ℂ → ℂ) ζ - (b : ℂ → ℂ) ζ
  rw [map_sub, ha, hb]

lemma isRealT_lapTest {c : testFn} (hc : IsRealT c) : IsRealT (lapTest c) := by
  rw [lapTest_eq_vf]
  exact isRealT_sub (isRealT_add (isRealT_vfTest _ (isRealT_vfTest _ hc))
    (isRealT_vfTest _ (isRealT_vfTest _ hc))) (isRealT_vfTest _ hc)

lemma isRealT_divImTest {c : testFn} (hc : IsRealT c) : IsRealT (divImTest c) := fun ζ => by
  show conj (invIm ζ * (c : ℂ → ℂ) ζ) = invIm ζ * (c : ℂ → ℂ) ζ
  rw [map_mul, hc, invIm, Complex.conj_ofReal]

/-! ### Conjugation commutes with `X`, `Y`, `Δ` -/

lemma vfTest_conjT (v : ℂ) (P : testFn) : vfTest v (conjT P) = conjT (vfTest v P) := by
  apply Subtype.ext; funext w
  show ((w.im : ℝ) : ℂ) * fderiv ℝ (fun x => conj ((P : ℂ → ℂ) x)) w v
    = conj (((w.im : ℝ) : ℂ) * fderiv ℝ (P : ℂ → ℂ) w v)
  rw [fderiv_conj_apply ((P.2.smooth.differentiable (by simp)) w) v, map_mul, Complex.conj_ofReal]

lemma conjT_add (P Q : testFn) : conjT (P + Q) = conjT P + conjT Q := by
  apply Subtype.ext; funext w
  show conj ((P : ℂ → ℂ) w + (Q : ℂ → ℂ) w) = conj ((P : ℂ → ℂ) w) + conj ((Q : ℂ → ℂ) w)
  rw [map_add]

lemma conjT_sub (P Q : testFn) : conjT (P - Q) = conjT P - conjT Q := by
  apply Subtype.ext; funext w
  show conj ((P : ℂ → ℂ) w - (Q : ℂ → ℂ) w) = conj ((P : ℂ → ℂ) w) - conj ((Q : ℂ → ℂ) w)
  rw [map_sub]

lemma lapTest_conjT (P : testFn) : lapTest (conjT P) = conjT (lapTest P) := by
  rw [lapTest_eq_vf, lapTest_eq_vf, vfTest_conjT, vfTest_conjT, vfTest_conjT, vfTest_conjT,
    conjT_sub, conjT_add]

/-- Mathlib's Laplacian on `ℂ` is `lapE`. -/
lemma laplacian_eq_lapE (f : ℂ → ℂ) (x : ℂ) : Δ f x = lapE f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  show iteratedFDeriv ℝ 2 f x ![1, 1] + iteratedFDeriv ℝ 2 f x ![Complex.I, Complex.I] = lapE f x
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  rfl

/-! ### The tempered identity `Δ_E(χu) = h` -/

local notation "L2C" => Lp ℂ 2 (volume : Measure ℂ)

/-- `θφ` as a test function. -/
noncomputable def thetaPhi (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) : testFn := smulTF φ hφ thetaT

/-- `c / y²`. -/
noncomputable def divIm2 (c : testFn) : testFn := divImTest (divImTest c)

lemma testFn_im_pos {c : testFn} {ζ : ℂ} (h : (c : ℂ → ℂ) ζ ≠ 0) : 0 < ζ.im :=
  c.2.inside (subset_tsupport _ h)

/-- `c · conj(θφ) = conj(y² φ · c/y²)` for a real test function `c` supported where `θ = 1`. -/
lemma mulT_conj_thetaPhi {c : testFn} (hc : IsRealT c)
    (hsupp : ∀ ζ, (c : ℂ → ℂ) ζ ≠ 0 → (thetaT : ℂ → ℂ) ζ = 1) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    mulT c (conjT (thetaPhi φ hφ))
      = conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ) (contDiff_imSq.mul hφ) (divIm2 c)) := by
  apply Subtype.ext; funext ζ
  show (c : ℂ → ℂ) ζ * conj (φ ζ * (thetaT : ℂ → ℂ) ζ)
    = conj (((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ * (invIm ζ * (invIm ζ * (c : ℂ → ℂ) ζ)))
  by_cases h0 : (c : ℂ → ℂ) ζ = 0
  · simp [h0]
  · have hy : 0 < ζ.im := testFn_im_pos h0
    rw [hsupp ζ h0, mul_one]
    have hyc : ((ζ.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
    have e : ((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ * (invIm ζ * (invIm ζ * (c : ℂ → ℂ) ζ)) = φ ζ * (c : ℂ → ℂ) ζ := by
      simp only [invIm]; push_cast; field_simp
    rw [e, map_mul, hc]
    ring

lemma support_sub_of_tsupport {c d : testFn} (h : tsupport (c : ℂ → ℂ) ⊆ tsupport (d : ℂ → ℂ))
    {ζ : ℂ} (hζ : (c : ℂ → ℂ) ζ ≠ 0) : ζ ∈ tsupport (d : ℂ → ℂ) := h (subset_tsupport _ hζ)

lemma theta_one_of_chi_tsupport {ζ : ℂ} (hζ : ζ ∈ tsupport (chiT : ℂ → ℂ)) : (thetaT : ℂ → ℂ) ζ = 1 :=
  (thetaT_eventuallyEq_one hζ).self_of_nhds

lemma tsupport_vfTest_sub (v : ℂ) (F : testFn) :
    tsupport ((vfTest v F : testFn) : ℂ → ℂ) ⊆ tsupport (F : ℂ → ℂ) :=
  (tsupport_mul_subset_right (f := fun w : ℂ => ((w.im : ℝ) : ℂ))).trans
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) v)

lemma tsupport_lapTest_sub (F : testFn) :
    tsupport ((lapTest F : testFn) : ℂ → ℂ) ⊆ tsupport (F : ℂ → ℂ) :=
  (tsupport_mul_subset_right (f := fun w : ℂ => ((w.im : ℝ) : ℂ) ^ 2)).trans (tsupport_lapE_subset F)

/-- `conj(y² (Δ_E φ) χ) = χ · Δ(conj(θφ))`. -/
lemma conj_lap_chi {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgφ : ∀ ζ, g ζ = lapE φ ζ) :
    conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * g ζ) (contDiff_imSq.mul hg) chiT)
      = mulT chiT (lapTest (conjT (thetaPhi φ hφ))) := by
  rw [lapTest_conjT]
  apply Subtype.ext; funext ζ
  show conj (((ζ.im : ℝ) : ℂ) ^ 2 * g ζ * (chiT : ℂ → ℂ) ζ)
    = (chiT : ℂ → ℂ) ζ * conj (((ζ.im : ℝ) : ℂ) ^ 2 * lapE (fun w => φ w * (thetaT : ℂ → ℂ) w) ζ)
  by_cases h0 : (chiT : ℂ → ℂ) ζ = 0
  · simp [h0]
  · have hζ : ζ ∈ tsupport (chiT : ℂ → ℂ) := subset_tsupport _ h0
    have hev : (fun w => φ w * (thetaT : ℂ → ℂ) w) =ᶠ[𝓝 ζ] φ := by
      filter_upwards [thetaT_eventuallyEq_one hζ] with w hw
      rw [hw, mul_one]
    have hlap : lapE (fun w => φ w * (thetaT : ℂ → ℂ) w) ζ = lapE φ ζ := by
      simp only [lapE, hev.fderiv.fderiv_eq]
    rw [hlap, ← hgφ, map_mul, map_mul, isRealT_chiT]
    ring

open FourierTransform SchwartzMap TemperedDistribution in
/-- The pairing of `E_c w` with a Schwartz function. -/
lemma pairing_eucL (c : testFn) (w : Lp ℂ 2 (volume : Measure ℍ)) (φ : 𝓢(ℂ, ℂ)) :
    ((eucL c w : L2C) : 𝓢'(ℂ, ℂ)) φ
      = inner ℂ (toL2 (conjT (smulTF (fun ζ => ((ζ.im : ℝ) : ℂ) ^ 2 * φ ζ)
          (contDiff_imSq.mul (φ.smooth ⊤)) c))) w := by
  rw [Lp.toTemperedDistribution_apply, ← integral_smul_eucFun c w (φ.smooth ⊤)]
  refine integral_congr_ae ?_
  filter_upwards [eucL_ae c w] with ζ h
  rw [h]

/-- `h = -χ(-Δu)/y² + 2(Xχ)(Xu)/y² + 2(Yχ)(Yu)/y² + (Δχ)u/y²` in `L²(ℂ)`. -/
noncomputable def hEuc (u : negLapH.domain) : L2C :=
  -eucL (divIm2 chiT) (negLapH u) + (2 : ℂ) • eucL (divIm2 (vfTest 1 chiT)) (domX u)
    + (2 : ℂ) • eucL (divIm2 (vfTest Complex.I chiT)) (domY u) + eucL (divIm2 (lapTest chiT)) u

lemma hsupp_of_sub {c : testFn} (h : tsupport (c : ℂ → ℂ) ⊆ tsupport (chiT : ℂ → ℂ)) :
    ∀ ζ, (c : ℂ → ℂ) ζ ≠ 0 → (thetaT : ℂ → ℂ) ζ = 1 := fun _ hζ =>
  theta_one_of_chi_tsupport (support_sub_of_tsupport h hζ)

open FourierTransform SchwartzMap TemperedDistribution in
/-- **`Δ_E(χu) = h` as tempered distributions**, for every `u ∈ Dom(-Δ)`. -/
theorem laplacian_eucL_chi (u : negLapH.domain) :
    Δ ((eucL chiT u : L2C) : 𝓢'(ℂ, ℂ)) = ((hEuc u : L2C) : 𝓢'(ℂ, ℂ)) := by
  ext φ
  have hφ := φ.smooth ⊤
  rw [TemperedDistribution.laplacian_apply_apply, pairing_eucL]
  have hΔ : ∀ ζ, (Δ φ : 𝓢(ℂ, ℂ)) ζ = lapE φ ζ := fun ζ => by
    rw [SchwartzMap.laplacian_apply, laplacian_eq_lapE]
  rw [conj_lap_chi hφ ((Δ φ).smooth ⊤) hΔ, inner_local_lap]
  have hX := tsupport_vfTest_sub 1 chiT
  have hY := tsupport_vfTest_sub Complex.I chiT
  have hL := tsupport_lapTest_sub chiT
  rw [mulT_conj_thetaPhi isRealT_chiT (hsupp_of_sub subset_rfl) hφ,
    mulT_conj_thetaPhi (isRealT_vfTest 1 isRealT_chiT) (hsupp_of_sub hX) hφ,
    mulT_conj_thetaPhi (isRealT_vfTest Complex.I isRealT_chiT) (hsupp_of_sub hY) hφ,
    mulT_conj_thetaPhi (isRealT_lapTest isRealT_chiT) (hsupp_of_sub hL) hφ]
  rw [hEuc, ← Lp.toTemperedDistributionCLM_apply (F := ℂ) (μ := volume)]
  simp only [map_add, map_neg, map_smul, Lp.toTemperedDistributionCLM_apply]
  simp only [add_apply, neg_apply, smul_apply, pairing_eucL, smul_eq_mul]

end Qschubert
