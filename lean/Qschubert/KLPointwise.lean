import Qschubert.KLSpecProd
import Qschubert.Statements

/-!
# Weak and classical words; the pointwise Dyson terms

The statement of Theorem 1.4R uses the classical `dysonP` and `approxAmp`, built from pointwise derivatives of a smooth
amplitude. The Dyson identities use the `L²` words `wordAct`. Here they are matched.

* `letC`, `wordC`: classical letters and words; `smoothH_wordC`;
* `ae_eq_of_inner_local`: a.e. equality on `{χ ≠ 0}` from pairing against test functions supported in `tsupport χ`;
* `domZ_classical`, `wordAct_classical`: for smooth `f` with `L²` class `a`, `wordAct S a =ᵐ wordC S f`;
* `polyC`, `polyC_mulP`, `lapT_eq_polyC`: classical word polynomials;
* `dysonP_eq`: `dysonP k t f = polyC (atT (dysT k) t) f`;
* `xK_ae`, `approxAmp_ae`: the `L²` Dyson terms are the classes of the pointwise ones.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-! ### Pairing and localization -/

lemma inner_congr_local (Q : testFn) {x y : L2H'} (h : ∀ᵐ z : ℍ ∂(volume : Measure ℍ), (Q : ℂ → ℂ) z ≠ 0 → x z = y z) :
    inner ℂ (toL2 Q) x = inner ℂ (toL2 Q) y := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [toL2_ae Q, h] with z h1 h2
  by_cases hQ : (Q : ℂ → ℂ) z = 0
  · simp only [h1, hQ, inner_zero_left]
  · rw [h2 hQ]

lemma inner_toL2_mulTL (χ P : testFn) (x : L2H') :
    inner ℂ (toL2 P) (mulTL χ x) = inner ℂ (toL2 (mulT (conjT χ) P)) x := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [toL2_ae P, mulTL_ae χ x, toL2_ae (mulT (conjT χ) P), repL2_ae x] with z h1 h2 h3 h4
  rw [h1, h2, h3, ← h4]
  show inner ℂ _ _ = inner ℂ (conj ((χ : ℂ → ℂ) z) * (P : ℂ → ℂ) z) _
  simp only [RCLike.inner_apply, map_mul, Complex.conj_conj]
  ring

lemma tsupport_mulT_conj_subset (χ P : testFn) :
    tsupport (mulT (conjT χ) P : ℂ → ℂ) ⊆ tsupport (χ : ℂ → ℂ) := by
  refine (tsupport_mul_subset_left (f := ((conjT χ : testFn) : ℂ → ℂ))).trans ?_
  exact tsupport_comp_subset (g := fun z : ℂ => conj z) (by simp) _

/-- A.e. equality on `{χ ≠ 0}`, from test functions supported in `tsupport χ`. -/
theorem ae_eq_of_inner_local {h h' : L2H'} {χ : testFn}
    (H : ∀ Q : testFn, tsupport (Q : ℂ → ℂ) ⊆ tsupport (χ : ℂ → ℂ) → inner ℂ (toL2 Q) h = inner ℂ (toL2 Q) h') :
    ∀ᵐ z : ℍ ∂(volume : Measure ℍ), (χ : ℂ → ℂ) z ≠ 0 → h z = h' z := by
  have e : mulTL χ h = mulTL χ h' := by
    refine ext_inner_left ℂ fun w => ?_
    refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
    · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
    · rw [inner_toL2_mulTL, inner_toL2_mulTL]
      exact H _ (tsupport_mulT_conj_subset χ P)
  have hae : ⇑(mulTL χ h) =ᵐ[volume] ⇑(mulTL χ h') := by rw [e]
  filter_upwards [hae, mulTL_ae χ h, mulTL_ae χ h', repL2_ae h, repL2_ae h'] with z h0 h1 h2 h3 h4 hχ
  rw [h1, h2] at h0
  rw [h3, h4]
  exact mul_left_cancel₀ hχ h0

/-! ### Classical letters and words -/

/-- The direction of a letter. -/
def vOf (z : Bool) : ℂ := if z then 1 else Complex.I

/-- A classical letter. -/
noncomputable def letC (z : Bool) (f : ℍ → ℂ) : ℍ → ℂ := if z then vecX f else vecY f

lemma letC_apply (z : Bool) (f : ℍ → ℂ) (w : ℍ) :
    letC z f w = ((w : ℂ).im : ℂ) * fderiv ℝ (extC f) (w : ℂ) (vOf z) := by
  cases z <;> rfl

/-- A classical word. -/
noncomputable def wordC : List Bool → (ℍ → ℂ) → ℍ → ℂ
  | [], f => f
  | z :: S, f => letC z (wordC S f)

lemma contDiff_im : ContDiff ℝ ∞ fun u : ℂ => ((u.im : ℝ) : ℂ) := (Complex.ofRealCLM.comp Complex.imCLM).contDiff

lemma smoothH_letC (z : Bool) {f : ℍ → ℂ} (hf : SmoothH f) : SmoothH (letC z f) := fun w => by
  set G : ℂ → ℂ := fun u => ((u.im : ℝ) : ℂ) * fderiv ℝ (extC f) u (vOf z)
  have hG : ∀ v : ℍ, letC z f v = G (v : ℂ) := fun v => letC_apply z f v
  have hd : ContDiffAt ℝ ∞ (fun u => fderiv ℝ (extC f) u (vOf z)) (w : ℂ) :=
    ((hf w).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  exact (contDiff_im.contDiffAt.mul hd).congr_of_eventuallyEq (extC_eventuallyEq hG w)

lemma smoothH_wordC : ∀ (S : List Bool) {f : ℍ → ℂ}, SmoothH f → SmoothH (wordC S f)
  | [], _, hf => hf
  | z :: S, _, hf => smoothH_letC z (smoothH_wordC S hf)

lemma differentiableAt_extC {f : ℍ → ℂ} (hf : SmoothH f) (w : ℍ) : DifferentiableAt ℝ (extC f) (w : ℂ) :=
  (hf w).differentiableAt (by simp)

lemma continuous_of_smoothH {f : ℍ → ℂ} (hf : SmoothH f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro w
  have h1 : ContinuousAt (extC f) (w : ℂ) := (hf w).continuousAt
  have h2 : ContinuousAt (fun v : ℍ => (v : ℂ)) w := UpperHalfPlane.continuous_coe.continuousAt
  have h3 := ContinuousAt.comp (f := fun v : ℍ => (v : ℂ)) (g := extC f) h1 h2
  refine h3.congr (Eventually.of_forall fun v => ?_)
  simp [extC, Function.comp, ofComplex_apply]

lemma smoothH_linear {f g : ℍ → ℂ} (hf : SmoothH f) (hg : SmoothH g) (c : ℂ) :
    SmoothH fun w => c * f w + g w := fun w =>
  (contDiffAt_const.mul (hf w)).add (hg w)

/-- The cutoff of a smooth function, as a test function. -/
noncomputable def cutF (η : testFn) {f : ℍ → ℂ} (hf : SmoothH f) : testFn :=
  ⟨fun w => extC f w * (η : ℂ → ℂ) w, isTestFn_mul_of_contDiffAt (fun w hw => hf ⟨w, hw⟩) η.2⟩

lemma cutF_coe (η : testFn) {f : ℍ → ℂ} (hf : SmoothH f) (w : ℂ) :
    ((cutF η hf : testFn) : ℂ → ℂ) w = extC f w * (η : ℂ → ℂ) w := rfl

lemma extC_coe (f : ℍ → ℂ) (w : ℍ) : extC f (w : ℂ) = f w := by
  simp [extC, ofComplex_apply]

lemma inner_domZ (z : Bool) (P : testFn) (u : negLapH.domain) :
    inner ℂ (toL2 (vfTest (vOf z) P)) (u : L2H')
      = -inner ℂ (toL2 P) (domZ z u) + (((vOf z).im : ℝ) : ℂ) * inner ℂ (toL2 P) (u : L2H') := by
  cases z
  · simpa [vOf, domZ] using inner_Y_dom P u
  · simpa [vOf, domZ] using inner_X_dom P u

/-- **A letter is the classical derivative.** -/
theorem domZ_classical (z : Bool) {f : ℍ → ℂ} (hf : SmoothH f) (u : negLapH.domain) (hu : ⇑(u : L2H') =ᵐ[volume] f) :
    ⇑(domZ z u) =ᵐ[volume] letC z f := by
  have hS : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  set χ : ℕ → testFn := fun k => cutT ((k : ℝ) + 1) (hS k) with hχ
  set η : ℕ → testFn := fun k => cutT (3 * ((k : ℝ) + 1)) (by positivity) with hη
  have hη1 : ∀ k, ∀ ζ ∈ tsupport (χ k : ℂ → ℂ), ∀ᶠ w in 𝓝 ζ, (η k : ℂ → ℂ) w = 1 := fun k ζ hζ =>
    cutS_three_eventuallyEq_one (hS k) hζ
  set F : ℕ → testFn := fun k => cutF (η k) hf with hF
  have hloc : ∀ k, ∀ᵐ x : ℍ ∂(volume : Measure ℍ), (χ k : ℂ → ℂ) x ≠ 0 →
      domZ z u x = toL2 (vfTest (vOf z) (F k)) x := fun k => by
    refine ae_eq_of_inner_local fun Q hQ => ?_
    have hpair : ∀ R : testFn, tsupport (R : ℂ → ℂ) ⊆ tsupport (χ k : ℂ → ℂ) →
        inner ℂ (toL2 R) (u : L2H') = inner ℂ (toL2 R) (toL2 (F k)) := fun R hR => by
      refine inner_congr_local R ?_
      filter_upwards [hu, toL2_ae (F k)] with x h1 h2 hx
      have hm : (x : ℂ) ∈ tsupport (χ k : ℂ → ℂ) := hR (subset_tsupport _ hx)
      rw [h1, h2, cutF_coe, (hη1 k _ hm).self_of_nhds, mul_one, extC_coe]
    have a1 := inner_domZ z Q u
    have a2 := inner_vf_left (vOf z) Q (F k)
    rw [hpair _ ((tsupport_vfTest_sub _ Q).trans hQ), hpair Q hQ] at a1
    rw [a2] at a1
    have := add_right_cancel a1
    exact (neg_inj.1 this).symm
  have hall := ae_all_iff.2 hloc
  have hall2 := ae_all_iff.2 fun k => toL2_ae (vfTest (vOf z) (F k))
  filter_upwards [hall, hall2] with x h1 h2
  obtain ⟨k, hk⟩ := (eventually_cutT (z := x)).exists
  have h1k : (χ k : ℂ → ℂ) x = 1 := (cutT_eventually (hS k) x.im_pos hk).1
  have hne : (χ k : ℂ → ℂ) x ≠ 0 := by rw [h1k]; exact one_ne_zero
  rw [h1 k hne, h2 k, vfTest_coe, letC_apply]
  have hm : (x : ℂ) ∈ tsupport (χ k : ℂ → ℂ) := subset_tsupport _ hne
  have hev : ((F k : testFn) : ℂ → ℂ) =ᶠ[𝓝 (x : ℂ)] extC f := by
    filter_upwards [hη1 k _ hm] with w hw
    rw [cutF_coe, hw, mul_one]
  rw [hev.fderiv_eq]

/-- **Weak words are classical words.** -/
theorem wordAct_classical {f : ℍ → ℂ} (hf : SmoothH f) {a : L2H'} (ha : ⇑a =ᵐ[volume] f) :
    ∀ S : List Bool, WordDom S a → ⇑(wordAct S a) =ᵐ[volume] wordC S f
  | [], _ => ha
  | z :: S, ⟨hS, hm⟩ => by
      rw [wordAct_cons z S hm]
      exact domZ_classical z (smoothH_wordC S hf) ⟨_, hm⟩ (wordAct_classical hf ha S hS)

/-! ### Linearity of classical words -/

lemma letC_linear (z : Bool) {f g : ℍ → ℂ} (hf : SmoothH f) (hg : SmoothH g) (c : ℂ) :
    letC z (fun w => c * f w + g w) = fun w => c * letC z f w + letC z g w := by
  funext w
  have h1 := (differentiableAt_extC hf w).hasFDerivAt
  have h2 := (differentiableAt_extC hg w).hasFDerivAt
  have e : extC (fun w => c * f w + g w) = fun u => c * extC f u + extC g u := rfl
  have h3 : HasFDerivAt (fun u => c * extC f u + extC g u) (c • fderiv ℝ (extC f) (w : ℂ) + fderiv ℝ (extC g) (w : ℂ)) (w : ℂ) :=
    (h1.const_mul c).add h2
  rw [letC_apply, letC_apply, letC_apply, e, h3.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma wordC_linear : ∀ (S : List Bool) {f g : ℍ → ℂ}, SmoothH f → SmoothH g → ∀ c : ℂ,
    wordC S (fun w => c * f w + g w) = fun w => c * wordC S f w + wordC S g w
  | [], _, _, _, _, _ => rfl
  | z :: S, _, _, hf, hg, c => by
      show letC z (wordC S _) = _
      rw [wordC_linear S hf hg c]
      exact letC_linear z (smoothH_wordC S hf) (smoothH_wordC S hg) c

lemma letC_zero (z : Bool) : letC z (fun _ => 0) = fun _ => 0 := by
  funext w
  have e : extC (fun _ : ℍ => (0 : ℂ)) = fun _ => 0 := rfl
  rw [letC_apply, e]
  simp

lemma wordC_zero : ∀ S : List Bool, wordC S (fun _ => 0) = fun _ => 0
  | [] => rfl
  | z :: S => by
      show letC z (wordC S _) = _
      rw [wordC_zero S, letC_zero]

lemma wordC_append : ∀ (S T : List Bool) (f : ℍ → ℂ), wordC (S ++ T) f = wordC S (wordC T f)
  | [], _, _ => rfl
  | z :: S, T, f => by
      show letC z (wordC (S ++ T) f) = letC z (wordC S (wordC T f))
      rw [wordC_append S T f]

/-! ### Classical word polynomials -/

/-- `Σ c_i Z_{w_i} f`, classically. -/
noncomputable def polyC (P : WP) (f : ℍ → ℂ) : ℍ → ℂ := fun z => (P.map fun t => t.1 * wordC t.2 f z).sum

lemma polyC_nil (f : ℍ → ℂ) : polyC [] f = fun _ => 0 := rfl

lemma polyC_cons (t : ℂ × List Bool) (P : WP) (f : ℍ → ℂ) :
    polyC (t :: P) f = fun z => t.1 * wordC t.2 f z + polyC P f z := by
  funext z; simp [polyC]

lemma polyC_append (P Q : WP) (f : ℍ → ℂ) : polyC (P ++ Q) f = fun z => polyC P f z + polyC Q f z := by
  funext z; simp [polyC]

lemma smoothH_zero : SmoothH (fun _ : ℍ => (0 : ℂ)) := fun _ => contDiffAt_const

lemma smoothH_polyC (P : WP) {f : ℍ → ℂ} (hf : SmoothH f) : SmoothH (polyC P f) := by
  induction P with
  | nil => exact smoothH_zero
  | cons t P ih =>
    rw [polyC_cons]
    exact smoothH_linear (smoothH_wordC _ hf) ih t.1

lemma wordC_polyC (S : List Bool) (Q : WP) {f : ℍ → ℂ} (hf : SmoothH f) :
    wordC S (polyC Q f) = polyC (Q.map fun q => (q.1, S ++ q.2)) f := by
  induction Q with
  | nil => exact wordC_zero S
  | cons q Q ih =>
    rw [polyC_cons, wordC_linear S (smoothH_wordC _ hf) (smoothH_polyC Q hf), ih, List.map_cons, polyC_cons]
    funext z
    rw [← wordC_append]

lemma polyC_map_mul (c : ℂ) (w : ℂ × List Bool → List Bool) (Q : WP) (f : ℍ → ℂ) (z : ℍ) :
    polyC (Q.map fun q => (c * q.1, w q)) f z = c * polyC (Q.map fun q => (q.1, w q)) f z := by
  induction Q with
  | nil => simp [polyC]
  | cons q Q ih =>
    simp only [List.map_cons, polyC_cons, ih]
    ring

/-- **Composition.** -/
theorem polyC_mulP (P Q : WP) {f : ℍ → ℂ} (hf : SmoothH f) : polyC P (polyC Q f) = polyC (mulP P Q) f := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    have e : mulP (p :: P) Q = (Q.map fun q => (p.1 * q.1, p.2 ++ q.2)) ++ mulP P Q := rfl
    rw [polyC_cons, e, polyC_append, ih, wordC_polyC _ _ hf]
    funext z
    rw [polyC_map_mul]

lemma lapT_eq_polyC (s : ℝ) (f : ℍ → ℂ) : lapT s f = polyC (deltaP s) f := by
  funext z
  simp only [lapT, polyC, deltaP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wordC, letC, ite_true,
    Bool.false_eq_true, ite_false]
  push_cast
  ring

/-- **`dysonP` is a classical word polynomial with time-dependent coefficients.** -/
theorem dysonP_eq {f : ℍ → ℂ} (hf : SmoothH f) : ∀ (k : ℕ) (t : ℝ), dysonP k t f = polyC (atT (dysT k) t) f
  | 0, t => by
      funext z
      simp [dysonP, atT, dysT, polyC, wordC]
  | k + 1, t => by
      funext z
      show ∫ s in (0 : ℝ)..t, lapT s (dysonP k s f) z = _
      have e : ∀ s, lapT s (dysonP k s f) z
          = ((mulTP deltaT (dysT k)).map fun r => r.1 s • wordC r.2 f z).sum := fun s => by
        rw [dysonP_eq hf k s, lapT_eq_polyC, polyC_mulP _ _ hf, ← atT_deltaT, ← atT_mulTP]
        simp [polyC, atT, Function.comp_def]
      simp_rw [e]
      rw [integral_list_sum (cont_mulTP cont_deltaT (cont_dysT k)) (fun w => wordC w f z) t]
      simp [polyC, atT, dysT, intTP, Function.comp_def]

/-! ### From `L²` to pointwise -/

section ae

variable {f : ℍ → ℂ} (hf : SmoothH f) {a : L2H'} (ha : ⇑a =ᵐ[volume] f) (hA : AllWords a)
include hf ha hA

theorem polyAct_ae (P : WP) : ⇑(polyAct P a) =ᵐ[volume] polyC P f := by
  induction P with
  | nil =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz
    rw [polyAct_nil, hz]; rfl
  | cons t P ih =>
    rw [polyAct_cons, polyC_cons]
    filter_upwards [Lp.coeFn_add (t.1 • wordAct t.2 a) (polyAct P a), Lp.coeFn_smul t.1 (wordAct t.2 a), ih,
      wordAct_classical hf ha t.2 (hA t.2)] with z h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

theorem xK_ae (k : ℕ) (t : ℝ) : ⇑(xK a k t) =ᵐ[volume] dysonP k t f := by
  rw [dysonP_eq hf]
  exact polyAct_ae hf ha hA _

/-- **The `L²` Dyson sum is the class of `approxAmp`.** -/
theorem approxAmp_ae (K : ℕ) (hb t : ℝ) :
    ⇑(∑ k ∈ Finset.range (K + 1), (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t) =ᵐ[volume] approxAmp K hb t f := by
  have key : ∀ m : ℕ, ⇑(∑ k ∈ Finset.range m, (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t)
      =ᵐ[volume] fun z => ∑ k ∈ Finset.range m, (Complex.I * (hb : ℂ) / 2) ^ k * dysonP k t f z := by
    intro m
    induction m with
    | zero =>
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz
      simp only [Finset.range_zero, Finset.sum_empty]
      rw [hz]; rfl
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      filter_upwards [Lp.coeFn_add (∑ k ∈ Finset.range m, (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t)
        ((Complex.I * (hb : ℂ) / 2) ^ m • xK a m t), Lp.coeFn_smul ((Complex.I * (hb : ℂ) / 2) ^ m) (xK a m t), ih,
        xK_ae hf ha hA m t] with z h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  exact key (K + 1)

end ae

lemma smoothH_dysonP {f : ℍ → ℂ} (hf : SmoothH f) (k : ℕ) (t : ℝ) : SmoothH (dysonP k t f) := by
  rw [dysonP_eq hf]; exact smoothH_polyC _ hf

lemma smoothH_approxAmp {f : ℍ → ℂ} (hf : SmoothH f) (K : ℕ) (hb t : ℝ) : SmoothH (approxAmp K hb t f) := by
  have key : ∀ m : ℕ, SmoothH fun z => ∑ k ∈ Finset.range m, (Complex.I * (hb : ℂ) / 2) ^ k * dysonP k t f z := by
    intro m
    induction m with
    | zero => simpa using smoothH_zero
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      have := smoothH_linear (smoothH_dysonP hf m t) ih ((Complex.I * (hb : ℂ) / 2) ^ m)
      have e : (fun z => ∑ k ∈ Finset.range m, (Complex.I * (hb : ℂ) / 2) ^ k * dysonP k t f z
            + (Complex.I * (hb : ℂ) / 2) ^ m * dysonP m t f z)
          = fun z => (Complex.I * (hb : ℂ) / 2) ^ m * dysonP m t f z
            + ∑ k ∈ Finset.range m, (Complex.I * (hb : ℂ) / 2) ^ k * dysonP k t f z := by
        funext z; ring
      rw [e]
      exact this
  exact key (K + 1)

end Qschubert
