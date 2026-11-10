import Qschubert.KLDD

/-!
# (D3) of `prop:dd-id` on `L²(ℍ)`: transport of `Δ^N` through `V(s)*`

With `P = e^{iφ/ħ}` (`phaseLp 1 ħ`), `S(s) = transportLp s`, and `w` a vector on which all words act:

* `mem_negLapH_of_weak`: the weak criterion for `Dom(-Δ)`; it uses that `-Δ` is essentially
  self-adjoint on test functions (`mem_graphBar_negLapH`);
* `inner_lapTest_phase_transport`: `⟪Δ P S(s) H, P S(s) w⟫ = ⟪H, Δ_φ(s) w⟫` for test `H`;
* `phase_transport_step`: `P S(s) w ∈ Dom(-Δ)` and `Δ (P S(s) w) = P S(s) Δ_φ(s) w`;
* `dd_D3_step`, `dd_D3`: `Δ^N (P V(s)* w) = P V(s)* Δ_φ(s)^N w`, in the iterated form `LapIter`.

This is the form used in the proof of (D4) (dd_appendix.tex, third bullet of (D4)):
`Δ^N(e^{iφ/ħ} V(s₁)* g) = e^{iφ/ħ} V(s₁)* Δ_φ(s₁)^N g`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ComplexConjugate InnerProductSpace

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **Weak criterion for `Dom(-Δ)`**: if `⟪ΔG, v⟫ = ⟪G, u⟫` for all test `G`, then `v ∈ Dom(-Δ)` and
`-Δ v = -u`. -/
theorem mem_negLapH_of_weak {v u : L2H'}
    (h : ∀ G : testFn, inner ℂ (toL2 (lapTest G)) v = inner ℂ (toL2 G) u) :
    ∃ hv : v ∈ negLapH.domain, negLapH ⟨v, hv⟩ = -u := by
  have key : ∀ p : graphBar, inner ℂ (-u) (p : L2H' × L2H').1 = inner ℂ v (p : L2H' × L2H').2 := by
    intro p
    refine DenseRange.induction_on denseRange_graphIncl p ?_ fun q => ?_
    · exact isClosed_eq (continuous_const.inner (continuous_fst.comp continuous_subtype_val))
        (continuous_const.inner (continuous_snd.comp continuous_subtype_val))
    · show inner ℂ (-u) (q : L2H' × L2H').1 = inner ℂ v (q : L2H' × L2H').2
      rw [← toL2_testOf q, ← neg_toL2_lapTest_testOf q, inner_neg_left, inner_neg_right,
        ← inner_conj_symm v, h, inner_conj_symm]
  have hall : ∀ x : negLapH.domain, inner ℂ (-u) (x : L2H') = inner ℂ v (negLapH x) := fun x =>
    key ⟨((x : L2H'), negLapH x), mem_graphBar_negLapH x⟩
  have hadj : v ∈ (LinearPMap.adjoint negLapH).domain :=
    LinearPMap.mem_adjoint_domain_of_exists v ⟨-u, hall⟩
  have hsa : LinearPMap.adjoint negLapH = negLapH := negLapH_isSelfAdjoint
  have hv : v ∈ negLapH.domain := by rw [← hsa]; exact hadj
  refine ⟨hv, ?_⟩
  have hval : LinearPMap.adjoint negLapH ⟨v, hadj⟩ = -u :=
    LinearPMap.adjoint_apply_eq negLapH_isSelfAdjoint.dense_domain ⟨v, hadj⟩ hall
  have : negLapH ⟨v, hv⟩ = LinearPMap.adjoint negLapH ⟨v, hadj⟩ :=
    ((LinearPMap.ext_iff.mp hsa).2 (x := v) (hf := hadj) (hg := hv)).symm
  rw [this, hval]

lemma phC_mul_neg (hb : ℝ) (w : ℂ) : phC hb w * phC (-hb) w = 1 := by
  simp only [phC, phG]
  rw [← Complex.exp_add]
  have : Complex.I * ((1 * -Real.log w.im / hb : ℝ) : ℂ) + Complex.I * ((1 * -Real.log w.im / -hb : ℝ) : ℂ) = 0 := by
    rw [div_neg]; push_cast; ring
  rw [this, Complex.exp_zero]

lemma phaseTest_phaseTest_neg (hb : ℝ) (F : testFn) : phaseTest hb (phaseTest (-hb) F) = F := by
  apply Subtype.ext; funext w
  show phC hb w * (phC (-hb) w * (F : ℂ → ℂ) w) = (F : ℂ → ℂ) w
  rw [← mul_assoc, phC_mul_neg, one_mul]

lemma transportTest_transportTest_neg (s : ℝ) (F : testFn) :
    transportTest s (transportTest (-s) F) = F := by
  apply Subtype.ext; funext w
  show ((Real.exp (-s / 2) : ℝ) : ℂ) * (((Real.exp (- -s / 2) : ℝ) : ℂ) * (F : ℂ → ℂ) (dilL (-s) (dilL s w)))
    = (F : ℂ → ℂ) w
  rw [show dilL (-s) (dilL s w) = w from (dilHomeo s).left_inv w, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add]
  rw [show -s / 2 + - -s / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]

lemma genYTest_eq (H : testFn) : genYTest H = vfTest Complex.I H - (1 / 2 : ℂ) • H := by
  apply Subtype.ext; funext w
  show genYFun H w = ((vfTest Complex.I H : testFn) : ℂ → ℂ) w - (1 / 2 : ℂ) * (H : ℂ → ℂ) w
  rw [vfTest_coe, genYFun]
  ring

lemma toL2_yyTest_eq (P : testFn) : toL2 (yyTest P) = toL2 (Yd (Yd P)) - toL2 (Yd P) := by
  rw [yyTest_eq, Yd, Yd, map_sub, map_sub, map_sub, map_sub, map_sub]
  abel

section
variable {w : L2H'} (hA : AllWords w)
include hA

/-- `⟪(e^{-2s}X² + Y² - Y) H, w⟫ = ⟪H, Δ(s) w⟫`. -/
lemma inner_lapTL2_words (s : ℝ) (H : testFn) :
    inner ℂ (lapTL2 s H) w = inner ℂ (toL2 H) (polyAct (deltaP s) w) := by
  have hw : w ∈ negLapH.domain := by simpa [wordAct] using AllWords.mem hA []
  rw [← lapTbar_eq_polyAct s ⟨w, hw⟩ hA, lapTL2_eq, lapTbar, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_psiX, inner_psiY, xxTest_eq, toL2_yyTest_eq]

/-- `⟪(Y - 1/2) H, w⟫ = ⟪H, w⟫/2 - ⟪H, Yw⟫`. -/
lemma inner_genY_words (H : testFn) :
    inner ℂ (toL2 (genYTest H)) w = (1 / 2 : ℂ) * inner ℂ (toL2 H) w - inner ℂ (toL2 H) (wordAct [false] w) := by
  have hw : w ∈ negLapH.domain := by simpa [wordAct] using AllWords.mem hA []
  have e : wordAct [false] w = domY ⟨w, hw⟩ := by
    rw [wordAct_cons false [] (show wordAct [] w ∈ negLapH.domain from hw)]
    simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  have h := inner_Y_dom H ⟨w, hw⟩
  change inner ℂ (toL2 (vfTest Complex.I H)) w = _ at h
  rw [genYTest_eq, map_sub, map_smul, inner_sub_left, inner_smul_left, h, e]
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-- `⟪Δ P S(s) H, P S(s) w⟫ = ⟪H, Δ_φ(s) w⟫`. -/
theorem inner_lapTest_phase_transport {hb : ℝ} (hb0 : hb ≠ 0) (s : ℝ) (H : testFn) :
    inner ℂ (toL2 (lapTest (phaseTest hb (transportTest s H)))) (phaseLp 1 hb (transportLp s w))
      = inner ℂ (toL2 H) (polyAct (deltaPhiP hb s) w) := by
  rw [lapTest_phaseTest hb0, toL2_phaseTest, LinearIsometry.inner_map_map]
  have hS : ∀ x : L2H', inner ℂ x (transportLp s w) = inner ℂ (transportLp (-s) x) w := by
    intro x
    have := inner_transportLp_neg (-s) x w
    rwa [neg_neg] at this
  rw [hS, map_sub, map_sub, map_smul, map_smul, genYTest_transportTest, map_sub, map_sub, map_smul,
    map_smul, toL2_transportTest, toL2_transportTest, transportLp_neg_comp, transportLp_neg_comp]
  rw [show transportLp (-s) (toL2 (lapTest (transportTest s H))) = lapTL2 s H from rfl,
    inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left, inner_lapTL2_words hA, inner_genY_words hA,
    deltaPhiP, polyAct_append, polyAct_cons, polyAct_cons, polyAct_nil, inner_add_right, inner_add_right,
    inner_add_right, inner_smul_right, inner_smul_right, inner_zero_right]
  have e0 : wordAct [] w = w := rfl
  rw [e0]
  have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
  simp only [map_div₀, map_mul, map_pow, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  field_simp
  ring

/-- `P S(s) w ∈ Dom(-Δ)`, and `Δ (P S(s) w) = P S(s) Δ_φ(s) w`. -/
theorem phase_transport_step {hb : ℝ} (hb0 : hb ≠ 0) (s : ℝ) :
    ∃ h : phaseLp 1 hb (transportLp s w) ∈ negLapH.domain,
      negLapH ⟨_, h⟩ = -phaseLp 1 hb (transportLp s (polyAct (deltaPhiP hb s) w)) := by
  refine mem_negLapH_of_weak fun G => ?_
  obtain ⟨H, rfl⟩ : ∃ H, G = phaseTest hb (transportTest s H) :=
    ⟨transportTest (-s) (phaseTest (-hb) G), by
      rw [transportTest_transportTest_neg, phaseTest_phaseTest_neg]⟩
  rw [inner_lapTest_phase_transport hA hb0, toL2_phaseTest, toL2_transportTest,
    LinearIsometry.inner_map_map, LinearIsometry.inner_map_map]

end

/-- `P V(s)* = e^{-is/(2ħ)} U(-s) P S(s)`. -/
lemma phase_dispVadj (hb s : ℝ) (w : L2H') :
    phaseLp 1 hb (dispVadj hb s w) = Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ))) •
      propH hb (-s) (phaseLp 1 hb (transportLp s w)) := by
  rw [dispVadj, map_smul, phaseLp_one_phaseLp_neg]

/-- **(D3), one step.** `P V(s)* w ∈ Dom(-Δ)` and `Δ (P V(s)* w) = P V(s)* Δ_φ(s) w`. -/
theorem dd_D3_step {hb : ℝ} (hb0 : hb ≠ 0) (s : ℝ) {w : L2H'} (hA : AllWords w) :
    ∃ h : phaseLp 1 hb (dispVadj hb s w) ∈ negLapH.domain,
      -negLapH ⟨_, h⟩ = phaseLp 1 hb (dispVadj hb s (polyAct (deltaPhiP hb s) w)) := by
  obtain ⟨h0, e0⟩ := phase_transport_step hA hb0 s
  obtain ⟨h1, e1⟩ := A_evol negLapH_isSelfAdjoint hb (-s) _ h0
  set c := Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ)))
  have hm : c • evol negLapH_isSelfAdjoint hb (-s) (phaseLp 1 hb (transportLp s w)) ∈ negLapH.domain :=
    Submodule.smul_mem _ _ h1
  have ep : phaseLp 1 hb (dispVadj hb s w)
      = c • evol negLapH_isSelfAdjoint hb (-s) (phaseLp 1 hb (transportLp s w)) := phase_dispVadj hb s w
  have ep2 := phase_dispVadj hb s (polyAct (deltaPhiP hb s) w)
  refine ⟨ep ▸ hm, ?_⟩
  have e2 : negLapH ⟨phaseLp 1 hb (dispVadj hb s w), ep ▸ hm⟩
      = c • negLapH ⟨_, h1⟩ := by
    have : (⟨phaseLp 1 hb (dispVadj hb s w), ep ▸ hm⟩ : negLapH.domain) = c • ⟨_, h1⟩ := Subtype.ext ep
    rw [this]
    exact negLapH.toFun.map_smul c _
  rw [e2, e1, e0, ep2, map_neg, smul_neg, neg_neg]
  rfl

/-- `LapIter N u v`: `u ∈ Dom(Δ^N)` and `Δ^N u = v`, with `Δ = -(-Δ)` iterated. -/
def LapIter : ℕ → L2H' → L2H' → Prop
  | 0, u, v => u = v
  | N + 1, u, v => ∃ h : u ∈ negLapH.domain, LapIter N (-negLapH ⟨u, h⟩) v

/-- One more step at the end of an iteration. -/
lemma LapIter.snoc : ∀ (N : ℕ) {u v v' : L2H'}, LapIter N u v →
    (∃ h : v ∈ negLapH.domain, -negLapH ⟨v, h⟩ = v') → LapIter (N + 1) u v'
  | 0, u, v, v', h, h' => by
      obtain rfl : u = v := h
      obtain ⟨hv, e⟩ := h'
      exact ⟨hv, e⟩
  | N + 1, u, v, v', ⟨h, hi⟩, h' => ⟨h, LapIter.snoc N hi h'⟩

/-- **(D3).** For `w` on which all words act, `P V(s)* w ∈ Dom(Δ^N)` and
`Δ^N (P V(s)* w) = P V(s)* Δ_φ(s)^N w`. -/
theorem dd_D3 {hb : ℝ} (hb0 : hb ≠ 0) (s : ℝ) (N : ℕ) {w : L2H'} (hA : AllWords w) :
    LapIter N (phaseLp 1 hb (dispVadj hb s w))
      (phaseLp 1 hb (dispVadj hb s (polyAct (powWP (deltaPhiP hb s) N) w))) := by
  induction N with
  | zero =>
    show phaseLp 1 hb (dispVadj hb s w) = phaseLp 1 hb (dispVadj hb s (polyAct (powWP (deltaPhiP hb s) 0) w))
    congr 2
    simp [powWP, oneP, polyAct, wordAct]
  | succ N ih =>
    refine LapIter.snoc N ih ?_
    rw [polyAct_powWP_succ hA]
    exact dd_D3_step hb0 s (allWords_polyAct hA _)

end Qschubert
