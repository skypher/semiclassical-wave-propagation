import Qschubert.EucLaplace
import Qschubert.GLInvariance
import Qschubert.PoincareP1

/-!
# The Sobolev bound `‖u‖_∞ ≤ K (‖u‖ + ‖(-Δ)u‖)` on `ℍ`

For `u ∈ Dom(-Δ)`: the energy identity `‖Xu‖² + ‖Yu‖² = Re⟪u, (-Δ)u⟫` (`energy_dom`) bounds
`‖h(u)‖ ≤ K₁ (‖u‖ + ‖(-Δ)u‖)` (`norm_hEuc_le`); `sobolevC` applied to `χu` and `h(u)`
(`laplacian_eucL_chi`) gives `|u| ≤ K (‖u‖ + ‖(-Δ)u‖)` a.e. on `|z - i| < 1/4` (`ae_bound_near_I`);
the isometries `g_{z₀} = [[y₀, x₀], [0, 1]]` (`negLapH_glU`, constants unchanged) carry it to
`|z - z₀| < y₀/4` (`ae_bound_near`), and a countable dense set of centres covers `ℍ`
(`sobolev_ae_bound`). This is the pointwise envelope of the manuscript's Lemma T (paper.tex:736).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Metric Physicslib4.Spectral.Unbounded
open scoped ContDiff ComplexConjugate InnerProductSpace

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- **Energy**: `‖Xu‖² + ‖Yu‖² = Re⟪u, (-Δ)u⟫`. -/
theorem energy_dom (u : negLapH.domain) :
    ‖domX u‖ ^ 2 + ‖domY u‖ ^ 2 = (inner ℂ (u : L2H) (negLapH u)).re := by
  set g : L2H := (u : L2H) + negLapH u
  have h := inner_formVec_lift_add g g
  have hR : formRes negLap g = (u : L2H) := formIncl_liftDom u
  rw [hR, show g - (u : L2H) = negLapH u from add_sub_cancel_left _ _] at h
  have e1 : ‖domX u‖ ^ 2 = (inner ℂ (domX u) (domX u)).re := by rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  have e2 : ‖domY u‖ ^ 2 = (inner ℂ (domY u) (domY u)).re := by rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  rw [e1, e2, ← Complex.add_re]
  have : inner ℂ (domX u) (domX u) + inner ℂ (domY u) (domY u) = inner ℂ (negLapH u) (u : L2H) := h
  rw [this, ← inner_conj_symm, Complex.conj_re]

lemma energy_le (u : negLapH.domain) : ‖domX u‖ ^ 2 + ‖domY u‖ ^ 2 ≤ ‖(u : L2H)‖ * ‖negLapH u‖ := by
  rw [energy_dom]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

lemma norm_dom_vf_le (u : negLapH.domain) :
    ‖domX u‖ ≤ ‖(u : L2H)‖ + ‖negLapH u‖ ∧ ‖domY u‖ ≤ ‖(u : L2H)‖ + ‖negLapH u‖ := by
  have h := energy_le u
  have ha := norm_nonneg (u : L2H)
  have hb := norm_nonneg (negLapH u)
  have hs : 0 ≤ ‖(u : L2H)‖ + ‖negLapH u‖ := by positivity
  have hsq : ‖(u : L2H)‖ * ‖negLapH u‖ ≤ (‖(u : L2H)‖ + ‖negLapH u‖) ^ 2 := by nlinarith
  constructor
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) hs two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖domY u‖]
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) hs two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖domX u‖]

/-- `K_h = sup|χ/y²| y + 2 sup|Xχ/y²| y + 2 sup|Yχ/y²| y + sup|Δχ/y²| y`. -/
noncomputable def Kh : ℝ :=
  supCy (divIm2 chiT) + 2 * supCy (divIm2 (vfTest 1 chiT)) + 2 * supCy (divIm2 (vfTest Complex.I chiT))
    + supCy (divIm2 (lapTest chiT))

lemma Kh_nonneg : 0 ≤ Kh := by
  unfold Kh
  have := supCy_nonneg (divIm2 chiT)
  have := supCy_nonneg (divIm2 (vfTest 1 chiT))
  have := supCy_nonneg (divIm2 (vfTest Complex.I chiT))
  have := supCy_nonneg (divIm2 (lapTest chiT))
  linarith

/-- `‖h(u)‖ ≤ K_h (‖u‖ + ‖(-Δ)u‖)`. -/
theorem norm_hEuc_le (u : negLapH.domain) : ‖hEuc u‖ ≤ Kh * (‖(u : L2H)‖ + ‖negLapH u‖) := by
  obtain ⟨hX, hY⟩ := norm_dom_vf_le u
  have h0 := norm_eucL_le (divIm2 chiT) (negLapH u)
  have h1 := norm_eucL_le (divIm2 (vfTest 1 chiT)) (domX u)
  have h2 := norm_eucL_le (divIm2 (vfTest Complex.I chiT)) (domY u)
  have h3 := norm_eucL_le (divIm2 (lapTest chiT)) (u : L2H)
  have s0 := supCy_nonneg (divIm2 chiT)
  have s1 := supCy_nonneg (divIm2 (vfTest 1 chiT))
  have s2 := supCy_nonneg (divIm2 (vfTest Complex.I chiT))
  have s3 := supCy_nonneg (divIm2 (lapTest chiT))
  have hu := norm_nonneg (u : L2H)
  have hv := norm_nonneg (negLapH u)
  have htri : ‖hEuc u‖ ≤ ‖eucL (divIm2 chiT) (negLapH u)‖ + 2 * ‖eucL (divIm2 (vfTest 1 chiT)) (domX u)‖
      + 2 * ‖eucL (divIm2 (vfTest Complex.I chiT)) (domY u)‖ + ‖eucL (divIm2 (lapTest chiT)) (u : L2H)‖ := by
    unfold hEuc
    refine norm_add₄_le.trans (le_of_eq ?_)
    rw [norm_neg, norm_smul, norm_smul]
    norm_num
  refine htri.trans ?_
  unfold Kh
  nlinarith [mul_le_mul_of_nonneg_left hX s1, mul_le_mul_of_nonneg_left hY s2]

/-- The local constant. -/
noncomputable def Kloc : ℝ :=
  ‖memLp_weightW.toLp weightW‖ * (supCy chiT + ‖twoPiSq⁻¹‖ * Kh)

lemma volume_preimage_coe_null' {T : Set ℂ} (hT : volume T = 0) :
    volume ((UpperHalfPlane.coe) ⁻¹' T : Set ℍ) = 0 := volume_preimage_coe_null hT

/-- **The fixed chart**: `|u| ≤ K_loc (‖u‖ + ‖(-Δ)u‖)` a.e. on `|z - i| < 1/4`. -/
theorem ae_bound_near_I (u : negLapH.domain) :
    ∀ᵐ (z : ℍ) ∂(volume : Measure ℍ), dist ((z : ℍ) : ℂ) Complex.I < 1 / 4 →
      ‖(u : L2H) z‖ ≤ Kloc * (‖(u : L2H)‖ + ‖negLapH u‖) := by
  obtain ⟨-, hae, hbd⟩ := sobolevC (eucL chiT u) (hEuc u) (laplacian_eucL_chi u)
  set B := Kloc * (‖(u : L2H)‖ + ‖negLapH u‖)
  have hB : ∀ ζ, ‖sobRep (eucL chiT u) (hEuc u) ζ‖ ≤ B := by
    intro ζ
    refine (hbd ζ).trans ?_
    have h1 := norm_eucL_le chiT (u : L2H)
    have h2 := norm_hEuc_le u
    have hw := norm_nonneg (memLp_weightW.toLp weightW)
    have hc := norm_nonneg twoPiSq⁻¹
    have hs := supCy_nonneg chiT
    unfold B Kloc
    have : ‖eucL chiT (u : L2H)‖ + ‖twoPiSq⁻¹‖ * ‖hEuc u‖
        ≤ (supCy chiT + ‖twoPiSq⁻¹‖ * Kh) * (‖(u : L2H)‖ + ‖negLapH u‖) := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hc, norm_nonneg (negLapH u), norm_nonneg (u : L2H)]
    calc ‖memLp_weightW.toLp weightW‖ * (‖eucL chiT (u : L2H)‖ + ‖twoPiSq⁻¹‖ * ‖hEuc u‖)
        ≤ ‖memLp_weightW.toLp weightW‖ * ((supCy chiT + ‖twoPiSq⁻¹‖ * Kh) * (‖(u : L2H)‖ + ‖negLapH u‖)) :=
          mul_le_mul_of_nonneg_left this hw
      _ = _ := by ring
  -- a.e. on `ℂ`
  have hC : ∀ᵐ ζ ∂(volume : Measure ℂ), ‖eucFun chiT (u : L2H) ζ‖ ≤ B := by
    filter_upwards [hae, eucL_ae chiT (u : L2H)] with ζ h1 h2
    rw [← h2, h1]; exact hB ζ
  -- pulled back to `ℍ`
  have hH : ∀ᵐ (z : ℍ) ∂(volume : Measure ℍ), ‖eucFun chiT (u : L2H) (z : ℂ)‖ ≤ B := by
    rw [ae_iff] at hC ⊢
    exact volume_preimage_coe_null' hC
  filter_upwards [hH, repL2_ae (u : L2H)] with z h1 h2 hz
  rw [h2]
  have hχ : (chiT : ℂ → ℂ) z = 1 := chiT_eq_one hz.le
  have : eucFun chiT (u : L2H) z = repL2 (u : L2H) z := by
    rw [eucFun, hχ, one_mul, ofComplex_apply]
  rw [← this]; exact h1

/-- `g_{z₀} • w = y₀ w + x₀`. -/
lemma toPointGL_smul_coe (z₀ w : ℍ) :
    ((toPointGL z₀ • w : ℍ) : ℂ) = (z₀.im : ℂ) * (w : ℂ) + (z₀.re : ℂ) := by
  rw [coe_smul_of_det_pos (by rw [toPointGL_det]; exact z₀.im_pos)]
  have h00 : ((toPointGL z₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = z₀.im := rfl
  have h01 : ((toPointGL z₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = z₀.re := rfl
  have h10 : ((toPointGL z₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := rfl
  have h11 : ((toPointGL z₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := rfl
  simp only [num, denom, h00, h01, h10, h11]
  simp

lemma dist_toPointGL (z₀ a b : ℍ) :
    dist ((toPointGL z₀ • a : ℍ) : ℂ) ((toPointGL z₀ • b : ℍ) : ℂ) = z₀.im * dist (a : ℂ) (b : ℂ) := by
  rw [toPointGL_smul_coe, toPointGL_smul_coe, Complex.dist_eq, Complex.dist_eq]
  rw [show (z₀.im : ℂ) * (a : ℂ) + (z₀.re : ℂ) - ((z₀.im : ℂ) * (b : ℂ) + (z₀.re : ℂ))
      = (z₀.im : ℂ) * ((a : ℂ) - (b : ℂ)) by ring, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z₀.im_pos]

/-- **Every centre**: `|u| ≤ K_loc (‖u‖ + ‖(-Δ)u‖)` a.e. on `|w - z₀| < y₀/4`. -/
theorem ae_bound_near (u : negLapH.domain) (z₀ : ℍ) :
    ∀ᵐ (w : ℍ) ∂(volume : Measure ℍ), dist ((w : ℍ) : ℂ) (z₀ : ℂ) < z₀.im / 4 →
      ‖(u : L2H) w‖ ≤ Kloc * (‖(u : L2H)‖ + ‖negLapH u‖) := by
  set g := toPointGL z₀
  obtain ⟨hv, hAv⟩ := negLapH_glU g u
  set v : negLapH.domain := ⟨glU g u, hv⟩
  have hnv : ‖(v : L2H)‖ = ‖(u : L2H)‖ := LinearIsometryEquiv.norm_map _ _
  have hnAv : ‖negLapH v‖ = ‖negLapH u‖ := by
    show ‖negLapH ⟨glU g u, hv⟩‖ = _
    rw [hAv, LinearIsometryEquiv.norm_map]
  have hloc := ae_bound_near_I v
  rw [hnv, hnAv] at hloc
  have hcomp : ∀ᵐ (z : ℍ) ∂(volume : Measure ℍ), dist ((z : ℍ) : ℂ) Complex.I < 1 / 4 →
      ‖(u : L2H) (g • z)‖ ≤ Kloc * (‖(u : L2H)‖ + ‖negLapH u‖) := by
    filter_upwards [hloc, glUL_ae g (u : L2H)] with z h1 h2 hz
    have := h1 hz
    rw [show ((v : L2H) : ℍ → ℂ) z = (glUL g (u : L2H)) z from rfl, h2] at this
    exact this
  have hpush := (measurePreserving_gl g⁻¹).quasiMeasurePreserving.ae hcomp
  filter_upwards [hpush] with w hw hdist
  have e : g • (g⁻¹ • w) = w := smul_inv_smul g w
  have hd : dist ((g⁻¹ • w : ℍ) : ℂ) Complex.I < 1 / 4 := by
    have h1 := dist_toPointGL z₀ (g⁻¹ • w) UpperHalfPlane.I
    rw [e, toPointGL_smul_I] at h1
    have hy := z₀.im_pos
    rw [h1] at hdist
    have : dist ((g⁻¹ • w : ℍ) : ℂ) ((UpperHalfPlane.I : ℍ) : ℂ) < 1 / 4 := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    simpa using this
  have := hw hd
  rwa [e] at this

/-- **The Sobolev bound on `ℍ`**: for `u ∈ Dom(-Δ)`, `|u| ≤ K_loc (‖u‖ + ‖(-Δ)u‖)` a.e., with
`K_loc` independent of `u`. -/
theorem sobolev_ae_bound (u : negLapH.domain) :
    ∀ᵐ (w : ℍ) ∂(volume : Measure ℍ), ‖(u : L2H) w‖ ≤ Kloc * (‖(u : L2H)‖ + ‖negLapH u‖) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℍ
  have hall : ∀ᵐ (w : ℍ) ∂(volume : Measure ℍ), ∀ z₀ : D, dist ((w : ℍ) : ℂ) ((z₀ : ℍ) : ℂ) < (z₀ : ℍ).im / 4 →
      ‖(u : L2H) w‖ ≤ Kloc * (‖(u : L2H)‖ + ‖negLapH u‖) := by
    have := hDc.to_subtype
    exact ae_all_iff.2 fun z₀ => ae_bound_near u z₀
  filter_upwards [hall] with w hw
  have hy := w.im_pos
  set U : Set ℍ := {z | dist (z : ℂ) (w : ℂ) < w.im / 8}
  have hU : IsOpen U := isOpen_lt (UpperHalfPlane.continuous_coe.dist continuous_const) continuous_const
  have hwU : w ∈ U := by show dist (w : ℂ) (w : ℂ) < w.im / 8; rw [dist_self]; positivity
  obtain ⟨z₀, hz₀D, hz₀U⟩ := hDd.exists_mem_open hU ⟨w, hwU⟩
  refine hw ⟨z₀, hz₀D⟩ ?_
  have h1 : dist (z₀ : ℂ) (w : ℂ) < w.im / 8 := hz₀U
  have h2 : |(z₀ : ℂ).im - (w : ℂ).im| ≤ dist (z₀ : ℂ) (w : ℂ) := by
    rw [Complex.dist_eq]; exact Complex.abs_im_le_norm _ |>.trans_eq' (by simp)
  have h3 : w.im - w.im / 8 < z₀.im := by
    have := (abs_le.1 h2).1
    simp only [UpperHalfPlane.coe_im] at this
    linarith
  show dist (w : ℂ) (z₀ : ℂ) < z₀.im / 4
  rw [dist_comm]
  linarith

end Qschubert
