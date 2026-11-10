import Qschubert.KLIntertwine
import Qschubert.PFIntertwine

/-!
# Modes of a test function in the Kontorovich–Lebedev picture

For a test function `F` on `ℍ` and `k ≠ 0`, the profile `y ↦ F̂(k, y)` of the partial Fourier transform
is smooth with compact support in `(0, ∞)` (`isKTest_prof`), and

  `(ΔF)^(k, y) = y² ∂_y² F̂(k, y) - 4π²k²y² F̂(k, y)`  (`prof_lapTest`).

With `c = 2π|k|` and the mode function `f_k(z) = √(c/z) F̂(k, z/c)` (`modeF`):

  `L f_k + f_k/4 = -(ΔF)_k`,  `L = -(z∂_z)² + z²`  (`Lop_modeF`),

so `KL((-ΔF)_k)(ν) = (ν² + 1/4) KL(f_k)(ν)`, and `∫ |f_k|² dz/z = ∫ |F̂(k, y)|² dy/y²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set UpperHalfPlane
open scoped ContDiff

/-- The profile `y ↦ F̂(k, y)`. -/
noncomputable def prof (F : ℂ → ℂ) (k : ℝ) (y : ℝ) : ℂ := pF F (k, y)

lemma hasDerivAt_prof (F : testFn) (k y : ℝ) :
    HasDerivAt (prof F k) (prof ((dirTest Complex.I F : testFn) : ℂ → ℂ) k y) y :=
  hasDerivAt_pF_y F k y

lemma deriv_prof (F : testFn) (k : ℝ) :
    deriv (prof F k) = prof ((dirTest Complex.I F : testFn) : ℂ → ℂ) k :=
  funext fun y => (hasDerivAt_prof F k y).deriv

lemma iteratedDeriv_prof (F : testFn) (k : ℝ) (n : ℕ) :
    iteratedDeriv n (prof F k) = prof (((dirTest Complex.I)^[n] F : testFn) : ℂ → ℂ) k := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_prof, ih, Function.iterate_succ_apply]

lemma support_prof_subset (F : testFn) (k : ℝ) :
    Function.support (prof F k) ⊆ Complex.im '' tsupport (F : ℂ → ℂ) := by
  intro y hy
  by_contra h
  apply hy
  have h0 : slice F y = 0 := by
    funext x
    show (F : ℂ → ℂ) ⟨x, y⟩ = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hx; exact h ⟨_, hx, rfl⟩
  simp only [prof, pF, h0]
  rw [Real.fourier_real_eq_integral_exp_smul]; simp

theorem isKTest_prof (F : testFn) (k : ℝ) : IsKTest (prof F k) := by
  have hK : IsCompact (Complex.im '' tsupport (F : ℂ → ℂ)) := F.2.compact.image Complex.continuous_im
  have hts : tsupport (prof F k) ⊆ Complex.im '' tsupport (F : ℂ → ℂ) :=
    closure_minimal (support_prof_subset F k) hK.isClosed
  refine ⟨?_, IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hts, ?_⟩
  · refine contDiff_of_differentiable_iteratedDeriv fun n _ => ?_
    rw [iteratedDeriv_prof]
    exact fun y => (hasDerivAt_prof _ k y).differentiableAt
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := hts hy
    exact F.2.inside hw

lemma prof_add (F G : testFn) (k : ℝ) :
    prof ((F + G : testFn) : ℂ → ℂ) k = prof F k + prof G k := by
  funext y
  show pF ((F + G : testFn) : ℂ → ℂ) (k, y) = pF F (k, y) + pF G (k, y)
  rw [pF_add]; rfl

lemma prof_sub (F G : testFn) (k : ℝ) :
    prof ((F - G : testFn) : ℂ → ℂ) k = prof F k - prof G k := by
  have h := prof_add (F - G) G k
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

lemma prof_vfX (F : testFn) (k y : ℝ) :
    prof ((vfTest 1 F : testFn) : ℂ → ℂ) k y = 2 * Real.pi * Complex.I * k * y * prof F k y :=
  pF_vfX F k y

lemma prof_vfY (F : testFn) (k : ℝ) :
    prof ((vfTest Complex.I F : testFn) : ℂ → ℂ) k = fun y : ℝ => (y : ℂ) * deriv (prof F k) y := by
  funext y; rw [deriv_prof]; exact pF_vfY F k y

/-- **`(ΔF)^(k, y) = y² ∂_y² F̂ - 4π²k²y² F̂`**. -/
theorem prof_lapTest (F : testFn) (k y : ℝ) :
    prof ((lapTest F : testFn) : ℂ → ℂ) k y
      = (y : ℂ) ^ 2 * deriv (deriv (prof F k)) y - 4 * Real.pi ^ 2 * k ^ 2 * y ^ 2 * prof F k y := by
  rw [lapTest_eq_vf, prof_sub, prof_add]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [prof_vfX, prof_vfX, prof_vfY (vfTest Complex.I F), prof_vfY F]
  have hd : HasDerivAt (fun y : ℝ => (y : ℂ) * deriv (prof F k) y)
      (1 * deriv (prof F k) y + (y : ℂ) * deriv (deriv (prof F k)) y) y := by
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
    have h2 : HasDerivAt (deriv (prof F k)) (deriv (deriv (prof F k)) y) y := by
      rw [deriv_prof]
      exact (hasDerivAt_prof _ k y).congr_deriv (by rw [deriv_prof])
    exact h1.mul h2
  beta_reduce
  rw [hd.deriv]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (4 * Real.pi ^ 2 * k ^ 2 * y ^ 2 * prof F k y) * hI

/-! ### Scaling and the mode function -/

lemma IsKTest.comp_div {g : ℝ → ℂ} (hg : IsKTest g) {c : ℝ} (hc : 0 < c) : IsKTest fun z => g (z / c) := by
  refine ⟨hg.smooth.comp (contDiff_id.div_const c), ?_, ?_⟩
  · have h := hg.compact.comp_smul (inv_ne_zero hc.ne')
    have e : (fun z => g (z / c)) = fun x => g (c⁻¹ • x) := by
      funext z; simp [smul_eq_mul, div_eq_inv_mul]
    rw [e]; exact h
  · refine (tsupport_comp_subset_preimage g (continuous_id.div_const c)).trans fun z hz => ?_
    have := hg.pos hz
    simp only [Set.mem_Ioi, id] at this ⊢
    exact (div_pos_iff_of_pos_right hc).1 this

lemma hasDerivAt_comp_div {g : ℝ → ℂ} (hg : IsKTest g) (c z : ℝ) :
    HasDerivAt (fun z => g (z / c)) (deriv g (z / c) / c) z := by
  have h := (hg.differentiable (z / c)).hasDerivAt.scomp z ((hasDerivAt_id' z).div_const c)
  refine h.congr_deriv ?_
  rw [Complex.real_smul]; push_cast; ring

/-- `c = 2π|k|`. -/
noncomputable def modeC (k : ℝ) : ℝ := 2 * Real.pi * |k|

lemma modeC_pos {k : ℝ} (hk : k ≠ 0) : 0 < modeC k := by
  unfold modeC; have := abs_pos.2 hk; positivity

lemma modeC_sq (k : ℝ) : (modeC k : ℂ) ^ 2 = 4 * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2 := by
  unfold modeC; push_cast
  have h : ((|k| : ℝ) : ℂ) ^ 2 = (k : ℂ) ^ 2 := by rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  linear_combination 4 * (Real.pi : ℂ) ^ 2 * h

/-- `s(z) = √(c/z) = √c / √z`. -/
noncomputable def sF (c z : ℝ) : ℝ := Real.sqrt c * (Real.sqrt z)⁻¹

lemma hasDerivAt_sF (c : ℝ) {z : ℝ} (hz : 0 < z) : HasDerivAt (sF c) (-sF c z / (2 * z)) z := by
  have hs := Real.hasDerivAt_sqrt hz.ne'
  have hsz : Real.sqrt z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
  have h := (hs.inv hsz).const_mul (Real.sqrt c)
  refine h.congr_deriv ?_
  simp only [sF]
  have hsq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz.le
  field_simp
  rw [hsq]

lemma hasDerivAt_sF' (c : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => -sF c z / (2 * z)) (3 * sF c z / (4 * z ^ 2)) z := by
  have h := ((hasDerivAt_sF c hz).neg).div ((hasDerivAt_id z).const_mul 2) (mul_ne_zero two_ne_zero hz.ne')
  refine h.congr_deriv ?_
  simp only [id, Pi.neg_apply]
  field_simp
  ring

/-- **The mode function** `f_k(z) = √(c/z) F̂(k, z/c)`, `c = 2π|k|`. -/
noncomputable def modeF (F : ℂ → ℂ) (k : ℝ) (z : ℝ) : ℂ :=
  ((sF (modeC k) z : ℝ) : ℂ) * prof F k (z / modeC k)

theorem isKTest_modeF (F : testFn) {k : ℝ} (hk : k ≠ 0) : IsKTest (modeF F k) := by
  have hv := (isKTest_prof F k).comp_div (modeC_pos hk)
  refine ⟨contDiff_iff_contDiffAt.2 fun z => ?_, hv.compact.mul_left,
    (tsupport_mul_subset_right (f := fun z : ℝ => ((sF (modeC k) z : ℝ) : ℂ))).trans hv.pos⟩
  by_cases hz : z ∈ tsupport fun z => prof F k (z / modeC k)
  · have hz0 : 0 < z := hv.pos hz
    have hs : ContDiffAt ℝ ∞ (fun z : ℝ => ((sF (modeC k) z : ℝ) : ℂ)) z := by
      refine Complex.ofRealCLM.contDiff.contDiffAt.comp z ?_
      exact contDiffAt_const.mul ((Real.contDiffAt_sqrt hz0.ne').inv (Real.sqrt_pos.2 hz0).ne')
    exact hs.mul hv.smooth.contDiffAt
  · have h := notMem_tsupport_iff_eventuallyEq.1 hz
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (h.mono fun y hy => by simp only [Pi.zero_apply] at hy; simp [modeF, hy])

/-- **`L f_k + f_k/4 = -(ΔF)_k`**. -/
theorem Lop_modeF (F : testFn) {k : ℝ} (hk : k ≠ 0) (z : ℝ) :
    Lop (modeF F k) z + (1 / 4 : ℂ) * modeF F k z = -modeF ((lapTest F : testFn) : ℂ → ℂ) k z := by
  set c := modeC k
  have hc : 0 < c := modeC_pos hk
  set u := prof F k
  have hu : IsKTest u := isKTest_prof F k
  set v : ℝ → ℂ := fun z => u (z / c)
  have hv : IsKTest v := hu.comp_div hc
  have hv1 : deriv v = fun z => deriv u (z / c) / c := funext fun z => (hasDerivAt_comp_div hu c z).deriv
  have hv2 : deriv (deriv v) = fun z => deriv (deriv u) (z / c) / c / c := by
    rw [hv1]; funext z
    exact ((hasDerivAt_comp_div hu.deriv' c z).div_const (c : ℂ)).deriv
  set φ : ℝ → ℂ := fun z => ((sF c z : ℝ) : ℂ)
  set φ' : ℝ → ℂ := fun z => ((-sF c z / (2 * z) : ℝ) : ℂ)
  set φ'' : ℝ → ℂ := fun z => ((3 * sF c z / (4 * z ^ 2) : ℝ) : ℂ)
  have hφ : ∀ z : ℝ, 0 < z → HasDerivAt φ (φ' z) z := fun z hz => (hasDerivAt_sF c hz).ofReal_comp
  have hφ' : ∀ z : ℝ, 0 < z → HasDerivAt φ' (φ'' z) z := fun z hz => (hasDerivAt_sF' c hz).ofReal_comp
  have hm : modeF F k = fun z => φ z * v z := rfl
  have hd1 : deriv (modeF F k) = fun z => φ' z * v z + φ z * deriv v z := by
    rw [hm]; funext z; exact (hasDerivAt_mul_of_tsupport hv hφ z).deriv
  have hd2 : deriv (deriv (modeF F k)) z
      = (φ'' z * v z + φ' z * deriv v z) + (φ' z * deriv v z + φ z * deriv (deriv v) z) := by
    rw [hd1]
    exact ((hasDerivAt_mul_of_tsupport hv hφ' z).add (hasDerivAt_mul_of_tsupport hv.deriv' hφ z)).deriv
  have hlap := prof_lapTest F k (z / c)
  simp only [Lop]
  rw [hd2, hd1]
  beta_reduce
  rw [show modeF ((lapTest F : testFn) : ℂ → ℂ) k z = φ z * prof ((lapTest F : testFn) : ℂ → ℂ) k (z / c) from rfl,
    hlap, show modeF F k z = φ z * v z from rfl]
  rcases le_or_gt z 0 with hz | hz
  · have e0 : v z = 0 := hv.eq_zero_of_nonpos hz
    have e1 : deriv v z = 0 := hv.deriv'.eq_zero_of_nonpos hz
    have e2 : deriv (deriv v) z = 0 := hv.deriv'.deriv'.eq_zero_of_nonpos hz
    have hzc : z / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg hz hc.le
    have f0 : prof F k (z / c) = 0 := hu.eq_zero_of_nonpos hzc
    have f2 : deriv (deriv (prof F k)) (z / c) = 0 := hu.deriv'.deriv'.eq_zero_of_nonpos hzc
    rw [e0, e1, e2, f0, f2]; ring
  · rw [hv2, hv1]
    simp only [v, u, φ, φ', φ'']
    have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hc2 := modeC_sq k
    rw [show (4 : ℂ) * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2 = (c : ℂ) ^ 2 from hc2.symm]
    push_cast
    field_simp
    ring

/-! ### KL of the modes -/

lemma IsKTest.Lop {f : ℝ → ℂ} (hf : IsKTest f) : IsKTest (Lop f) := by
  have h1 := hf.deriv'
  have h2 := h1.deriv'
  have hz2 : ContDiff ℝ ∞ fun z : ℝ => (z : ℂ) ^ 2 := (Complex.ofRealCLM.contDiff).pow 2
  have hz : ContDiff ℝ ∞ fun z : ℝ => (z : ℂ) := Complex.ofRealCLM.contDiff
  refine ⟨((hz2.mul h2.smooth).neg.sub (hz.mul h1.smooth)).add (hz2.mul hf.smooth), ?_, ?_⟩
  · exact ((h2.compact.mul_left.neg).sub h1.compact.mul_left).add hf.compact.mul_left
  · refine (tsupport_add _ _).trans (Set.union_subset ((tsupport_sub _ _).trans (Set.union_subset ?_ ?_)) ?_)
    · exact (tsupport_neg _).le.trans ((tsupport_mul_subset_right (f := fun z : ℝ => (z : ℂ) ^ 2)).trans h2.pos)
    · exact (tsupport_mul_subset_right (f := fun z : ℝ => (z : ℂ))).trans h1.pos
    · exact (tsupport_mul_subset_right (f := fun z : ℝ => (z : ℂ) ^ 2)).trans hf.pos

lemma integrable_klT_integrand {f : ℝ → ℂ} (hf : IsKTest f) (ν : ℝ) :
    Integrable fun z => besselKn 0 (ν * Complex.I) z * ((z : ℂ)⁻¹ * f z) :=
  integrable_mul_of_tsupport hf.inv_mul (continuousOn_besselKn 0 _)

/-- Linearity of the KL transform on test functions. -/
lemma klT_linear {f g : ℝ → ℂ} (hf : IsKTest f) (hg : IsKTest g) (a b : ℂ) (ν : ℝ) :
    klT (fun z => a * f z + b * g z) ν = a * klT f ν + b * klT g ν := by
  rw [klT_eq_integral (fun z hz => by rw [hf.eq_zero_of_nonpos hz, hg.eq_zero_of_nonpos hz]; ring),
    klT_eq_integral (fun z hz => hf.eq_zero_of_nonpos hz), klT_eq_integral (fun z hz => hg.eq_zero_of_nonpos hz),
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← integral_add ((integrable_klT_integrand hf ν).const_mul a) ((integrable_klT_integrand hg ν).const_mul b)]
  congr 1; funext z; ring

/-- **`KL((ΔF)_k)(ν) = -(ν² + 1/4) KL(f_k)(ν)`**. -/
theorem klT_modeF_lap (F : testFn) {k : ℝ} (hk : k ≠ 0) (ν : ℝ) :
    klT (modeF ((lapTest F : testFn) : ℂ → ℂ) k) ν = -((ν : ℂ) ^ 2 + 1 / 4) * klT (modeF F k) ν := by
  have hm := isKTest_modeF F hk
  have e : modeF ((lapTest F : testFn) : ℂ → ℂ) k = fun z => (-1 : ℂ) * Lop (modeF F k) z + (-1 / 4 : ℂ) * modeF F k z := by
    funext z; linear_combination (Lop_modeF F hk z)
  rw [e, klT_linear hm.Lop hm, klT_Lop hm]; ring

lemma sF_sq {c z : ℝ} (hc : 0 ≤ c) (hz : 0 < z) : sF c z ^ 2 = c / z := by
  rw [sF, mul_pow, inv_pow, Real.sq_sqrt hc, Real.sq_sqrt hz.le, div_eq_mul_inv]

/-- **Per-mode Parseval**: `∫_0^∞ w(ν)|KL(f_k)(ν)|² dν = ∫_0^∞ |F̂(k, y)|² dy/y²`. -/
theorem kl_parseval_modeF (F : testFn) {k : ℝ} (hk : k ≠ 0) :
    ∫ ν in Ioi 0, 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) * ‖klT (modeF F k) ν‖ ^ 2
      = ∫ y in Ioi 0, ‖prof F k y‖ ^ 2 / y ^ 2 := by
  rw [kl_parseval (isKTest_modeF F hk)]
  set c := modeC k
  have hc : 0 < c := modeC_pos hk
  set G : ℝ → ℝ := fun z => ‖modeF F k z‖ ^ 2 / z
  have hsub := integral_comp_mul_left_Ioi G 0 hc
  rw [mul_zero] at hsub
  have hpt : ∀ y ∈ Ioi (0 : ℝ), G (c * y) = c⁻¹ * (‖prof F k y‖ ^ 2 / y ^ 2) := by
    intro y hy
    have hy0 : 0 < y := hy
    have hcy : 0 < c * y := mul_pos hc hy0
    simp only [G, modeF, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [sF_sq hc.le hcy, show c * y / c = y by field_simp]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, MeasureTheory.integral_const_mul, smul_eq_mul] at hsub
  have : ∫ z in Ioi (0 : ℝ), G z = c * (c⁻¹ * ∫ y in Ioi 0, ‖prof F k y‖ ^ 2 / y ^ 2) := by
    rw [hsub]; field_simp
  rw [this]; field_simp

end Qschubert
