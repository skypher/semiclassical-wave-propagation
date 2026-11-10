import Qschubert.KLWB
import Qschubert.VAdjPathBar

/-!
# The Dyson identity behind (D1), (D2) of `prop:dd-id`

`thm:dd-appx` uses (D1) and (D2) only through
`a - V(t)* a^{(K)}(t) = c^{K+1} ∫_{Σ_{K+1}(t)} V(s₁)* Δ(s₁)⋯Δ(s_{K+1}) a ds` (dd_appendix.tex, proof of (D4)).
This identity is proved directly (`dd_D12`, `dd_D12_simplex`): `V` only stands on the left, so the
all-words class has to be preserved by nothing but the Dyson polynomials themselves, not by the propagators.

* `TP`: word polynomials with time-dependent coefficients; `dysT k` is `P_k(t)`; `xK a k t = P_k(t) a` is a finite sum
  `Σ f_i(t) Z_{w_i} a`.
* `simplexInt k t Φ = ∫_{t > s₁ > ⋯ > s_k > 0} Φ(s₁, …, s_k) ds`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- Word polynomials with time-dependent coefficients. -/
abbrev TP := List ((ℝ → ℂ) × List Bool)

def atT (R : TP) (s : ℝ) : WP := R.map fun r => (r.1 s, r.2)

def mulTP (R Q : TP) : TP := R.flatMap fun r => Q.map fun q => (fun s => r.1 s * q.1 s, r.2 ++ q.2)

def constTP (Q : WP) : TP := Q.map fun q => (fun _ => q.1, q.2)

noncomputable def intTP (R : TP) : TP := R.map fun r => (fun t => ∫ s in (0 : ℝ)..t, r.1 s, r.2)

noncomputable def deltaT : TP :=
  [(fun s => ((Real.exp (-2 * s) : ℝ) : ℂ), [true, true]), (fun _ => 1, [false, false]), (fun _ => -1, [false])]

/-- `P_k(t)` as a time-dependent word polynomial. -/
noncomputable def dysT : ℕ → TP
  | 0 => [(fun _ => 1, [])]
  | k + 1 => intTP (mulTP deltaT (dysT k))

lemma atT_mulTP (R Q : TP) (s : ℝ) : atT (mulTP R Q) s = mulP (atT R s) (atT Q s) := by
  simp [atT, mulTP, mulP, List.map_flatMap, List.flatMap_map, Function.comp_def]

lemma atT_constTP (Q : WP) (s : ℝ) : atT (constTP Q) s = Q := by
  simp [atT, constTP, Function.comp_def]

lemma atT_deltaT (s : ℝ) : atT deltaT s = deltaP s := rfl

/-- Continuous coefficients. -/
def Cont (R : TP) : Prop := ∀ r ∈ R, Continuous r.1

lemma cont_mulTP {R Q : TP} (hR : Cont R) (hQ : Cont Q) : Cont (mulTP R Q) := by
  intro t ht
  simp only [mulTP, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨r, hr, q, hq, rfl⟩ := ht
  exact (hR r hr).mul (hQ q hq)

lemma cont_constTP (Q : WP) : Cont (constTP Q) := by
  intro t ht
  simp only [constTP, List.mem_map] at ht
  obtain ⟨q, _, rfl⟩ := ht
  exact continuous_const

lemma cont_intTP {R : TP} (hR : Cont R) : Cont (intTP R) := by
  intro t ht
  simp only [intTP, List.mem_map] at ht
  obtain ⟨r, hr, rfl⟩ := ht
  exact intervalIntegral.continuous_primitive (fun a b => (hR r hr).intervalIntegrable a b) 0

lemma cont_deltaT : Cont deltaT := by
  intro t ht
  simp only [deltaT, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact Complex.continuous_ofReal.comp (by fun_prop)
  · exact continuous_const
  · exact continuous_const

lemma cont_dysT (k : ℕ) : Cont (dysT k) := by
  induction k with
  | zero =>
    intro t ht
    simp only [dysT, List.mem_singleton] at ht
    subst ht
    exact continuous_const
  | succ k ih => exact cont_intTP (cont_mulTP cont_deltaT ih)

section path

variable {a : L2H'} (hA : AllWords a)

omit hA in
lemma continuous_polyAct_atT {R : TP} (hR : Cont R) : Continuous fun s => polyAct (atT R s) a := by
  induction R with
  | nil => exact continuous_const
  | cons r R ih =>
    have e : (fun s => polyAct (atT (r :: R) s) a) = fun s => r.1 s • wordAct r.2 a + polyAct (atT R s) a := by
      funext s; exact polyAct_cons (r.1 s, r.2) (atT R s) a
    rw [e]
    exact ((hR r (by simp)).smul continuous_const).add (ih fun q hq => hR q (by simp [hq]))

omit hA in
lemma hasDerivAt_polyAct_intTP {R : TP} (hR : Cont R) (s : ℝ) :
    HasDerivAt (fun t => polyAct (atT (intTP R) t) a) (polyAct (atT R s) a) s := by
  induction R with
  | nil => exact hasDerivAt_const s _
  | cons r R ih =>
    have e : (fun t => polyAct (atT (intTP (r :: R)) t) a)
        = fun t => (∫ x in (0 : ℝ)..t, r.1 x) • wordAct r.2 a + polyAct (atT (intTP R) t) a := by
      funext t; exact polyAct_cons ((∫ x in (0 : ℝ)..t, r.1 x), r.2) (atT (intTP R) t) a
    have e' : polyAct (atT (r :: R) s) a = r.1 s • wordAct r.2 a + polyAct (atT R s) a :=
      polyAct_cons (r.1 s, r.2) (atT R s) a
    rw [e, e']
    have hc := hR r (by simp)
    have h1 : HasDerivAt (fun t => ∫ x in (0 : ℝ)..t, r.1 x) (r.1 s) s :=
      intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    exact (h1.smul_const _).add (ih fun q hq => hR q (by simp [hq]))

omit hA in
lemma polyAct_intTP_zero (R : TP) : polyAct (atT (intTP R) 0) a = 0 := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    have e : polyAct (atT (intTP (r :: R)) 0) a
        = (∫ x in (0 : ℝ)..0, r.1 x) • wordAct r.2 a + polyAct (atT (intTP R) 0) a :=
      polyAct_cons ((∫ x in (0 : ℝ)..0, r.1 x), r.2) (atT (intTP R) 0) a
    rw [e, ih, intervalIntegral.integral_same, zero_smul, add_zero]

include hA

lemma mem_polyAct (P : WP) : polyAct P a ∈ negLapH.domain := by
  have h := (allWords_polyAct hA P) [true]
  exact h.2

/-- `-Δ u = -Δ(0) u` as a word polynomial. -/
lemma negLapH_eq_poly (P : WP) : negLapH ⟨polyAct P a, mem_polyAct hA P⟩ = -polyAct (deltaP 0) (polyAct P a) := by
  have hl := lapTbar_eq_polyAct 0 ⟨polyAct P a, mem_polyAct hA P⟩ (allWords_polyAct hA P)
  rw [lapTbar_zero] at hl
  exact neg_eq_iff_eq_neg.1 hl

/-- The path `s ↦ (P(s)a, -ΔP(s)a)` in the graph closure. -/
noncomputable def pathG (R : TP) (s : ℝ) : graphBar :=
  ⟨(polyAct (atT R s) a, negLapH ⟨polyAct (atT R s) a, mem_polyAct hA _⟩),
    mem_graphBar_negLapH ⟨polyAct (atT R s) a, mem_polyAct hA _⟩⟩

lemma continuous_pathG {R : TP} (hR : Cont R) : Continuous (pathG hA R) := by
  refine Continuous.subtype_mk (Continuous.prodMk (continuous_polyAct_atT hR) ?_) _
  have e : (fun s => negLapH ⟨polyAct (atT R s) a, mem_polyAct hA _⟩)
      = fun s => -polyAct (atT (mulTP (constTP (deltaP 0)) R) s) a := by
    funext s
    rw [negLapH_eq_poly hA, polyAct_mulP hA, atT_mulTP, atT_constTP]
  rw [e]
  exact (continuous_polyAct_atT (cont_mulTP (cont_constTP _) hR)).neg

lemma lapTbar_pathG (R : TP) (s t : ℝ) :
    lapTbar t (pathG hA R s) = polyAct (deltaP t) (polyAct (atT R s) a) :=
  lapTbar_eq_polyAct t ⟨polyAct (atT R s) a, mem_polyAct hA _⟩ (allWords_polyAct hA _)

/-- **The moving-input Duhamel formula for a Dyson-type polynomial.** -/
theorem path_integral {hb : ℝ} (hb0 : hb ≠ 0) {Q : TP} (hQ : Cont Q) (t : ℝ) :
    dispVadj hb t (polyAct (atT (intTP Q) t) a)
      = ∫ s in (0 : ℝ)..t, (dispVadj hb s (polyAct (atT Q s) a)
          - (Complex.I * (hb : ℂ) / 2) • dispVadj hb s (polyAct (deltaP s) (polyAct (atT (intTP Q) s) a))) := by
  have hint := cont_intTP hQ
  have h := dispVadj_path_bar_sub_eq_integral hb0 (pathG hA (intTP Q)) (fun s => polyAct (atT Q s) a)
    (fun s => hasDerivAt_polyAct_intTP hQ s) (continuous_polyAct_atT hQ) (continuous_pathG hA hint) t
  have e0 : ((pathG hA (intTP Q) 0 : graphBar) : L2H' × L2H').1 = 0 := polyAct_intTP_zero Q
  have e1 : ((pathG hA (intTP Q) t : graphBar) : L2H' × L2H').1 = polyAct (atT (intTP Q) t) a := rfl
  rw [e0, e1, sub_zero] at h
  rw [h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [lapTbar_pathG]

end path

/-- `P_k(t) a`. -/
noncomputable def xK (a : L2H') (k : ℕ) (t : ℝ) : L2H' := polyAct (atT (dysT k) t) a

lemma xK_zero (a : L2H') (t : ℝ) : xK a 0 t = a := by
  simp [xK, atT, dysT, polyAct, wordAct]

/-- `V(s)*` as a linear map. -/
noncomputable def dispVadjL (hb s : ℝ) : L2H' →ₗ[ℂ] L2H' where
  toFun := dispVadj hb s
  map_add' x y := by simp only [dispVadj, map_add, smul_add]
  map_smul' c x := by
    simp only [dispVadj, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

lemma dispVadjL_apply (hb s : ℝ) (x : L2H') : dispVadjL hb s x = dispVadj hb s x := rfl

/-- `J_k(t) = ∫₀ᵗ V(s)* Δ(s) P_k(s) a ds`. -/
noncomputable def jK (hb : ℝ) (a : L2H') (k : ℕ) (t : ℝ) : L2H' :=
  ∫ s in (0 : ℝ)..t, dispVadj hb s (polyAct (deltaP s) (xK a k s))

section identity

variable {a : L2H'} (hA : AllWords a) {hb : ℝ} (hb0 : hb ≠ 0)
include hA

lemma poly_delta_xK (k : ℕ) (s : ℝ) :
    polyAct (deltaP s) (xK a k s) = polyAct (atT (mulTP deltaT (dysT k)) s) a := by
  rw [xK, polyAct_mulP hA, atT_mulTP, atT_deltaT]

lemma continuous_integrand (k : ℕ) : Continuous fun s => dispVadj hb s (polyAct (deltaP s) (xK a k s)) := by
  have h : (fun s => dispVadj hb s (polyAct (deltaP s) (xK a k s)))
      = fun s => dispVadj hb s (polyAct (atT (mulTP deltaT (dysT k)) s) a) := by
    funext s; rw [poly_delta_xK hA]
  rw [h]
  refine continuous_iff_continuousAt.2 fun s => tendsto_dispVadj (continuous_id.tendsto s) ?_
  exact (continuous_polyAct_atT (cont_mulTP cont_deltaT (cont_dysT k))).tendsto s

include hb0

/-- `V(t)* a - a = -c J₀(t)`. -/
lemma G_zero (t : ℝ) : dispVadj hb t a - a = -(Complex.I * (hb : ℂ) / 2) • jK hb a 0 t := by
  have hmem : a ∈ negLapH.domain := (hA [true]).2
  have h := dispVadj_sub_eq_integral_bar hb0 t ⟨(a, negLapH ⟨a, hmem⟩), mem_graphBar_negLapH ⟨a, hmem⟩⟩
  refine h.trans ?_
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [xK_zero]
  rw [lapTbar_eq_polyAct s ⟨a, hmem⟩ hA]

/-- `V(t)* P_{k+1}(t) a = J_k(t) - c J_{k+1}(t)`. -/
lemma G_succ (k : ℕ) (t : ℝ) :
    dispVadj hb t (xK a (k + 1) t) = jK hb a k t - (Complex.I * (hb : ℂ) / 2) • jK hb a (k + 1) t := by
  have h := path_integral hA hb0 (cont_mulTP cont_deltaT (cont_dysT k)) t
  have c1 := continuous_integrand hA (hb := hb) k
  have c2 := continuous_integrand hA (hb := hb) (k + 1)
  have e1 : ∀ s, dispVadj hb s (polyAct (atT (mulTP deltaT (dysT k)) s) a)
      = dispVadj hb s (polyAct (deltaP s) (xK a k s)) := fun s => by rw [poly_delta_xK hA]
  show dispVadj hb t (polyAct (atT (intTP (mulTP deltaT (dysT k))) t) a) = _
  rw [h]
  simp_rw [e1]
  set c : ℂ := Complex.I * (hb : ℂ) / 2
  have hs : ∫ s in (0 : ℝ)..t, (dispVadj hb s (polyAct (deltaP s) (xK a k s))
        - c • dispVadj hb s (polyAct (deltaP s) (xK a (k + 1) s)))
      = (∫ s in (0 : ℝ)..t, dispVadj hb s (polyAct (deltaP s) (xK a k s)))
        - c • ∫ s in (0 : ℝ)..t, dispVadj hb s (polyAct (deltaP s) (xK a (k + 1) s)) := by
    have c3 : Continuous fun s => c • dispVadj hb s (polyAct (deltaP s) (xK a (k + 1) s)) := c2.const_smul c
    rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c3.intervalIntegrable _ _),
      intervalIntegral.integral_smul]
  exact hs

/-- **The combined identity (D1) + (D2).** With `c = iħ/2`,
`a - V(t)* Σ_{k≤K} c^k P_k(t) a = c^{K+1} ∫₀ᵗ V(s)* Δ(s) P_K(s) a ds`. -/
theorem dd_D12 (K : ℕ) (t : ℝ) :
    a - dispVadj hb t (∑ k ∈ Finset.range (K + 1), (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t)
      = (Complex.I * (hb : ℂ) / 2) ^ (K + 1) • jK hb a K t := by
  set c : ℂ := Complex.I * (hb : ℂ) / 2
  have hL : ∀ (K : ℕ), dispVadj hb t (∑ k ∈ Finset.range (K + 1), c ^ k • xK a k t)
      = ∑ k ∈ Finset.range (K + 1), c ^ k • dispVadj hb t (xK a k t) := fun K => by
    simp only [← dispVadjL_apply, map_sum, map_smul]
  rw [hL]
  induction K with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_smul, xK_zero, pow_one]
    have h := G_zero hA hb0 t
    rw [show dispVadj hb t a = a + -(c • jK hb a 0 t) by
      rw [← neg_smul]; exact eq_add_of_sub_eq' h]
    abel
  | succ K ih =>
    rw [Finset.sum_range_succ, G_succ hA hb0, ← sub_sub, ih, smul_sub, smul_smul, pow_succ (c) (K + 1)]
    abel

end identity

/-! ### The simplex form -/

/-- `∫_{t > s₁ > ⋯ > s_k > 0} Φ(s₁, …, s_k) ds`. -/
noncomputable def simplexInt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : ℕ → ℝ → (List ℝ → E) → E
  | 0, _, Φ => Φ []
  | k + 1, t, Φ => ∫ s in (0 : ℝ)..t, simplexInt k s fun l => Φ (s :: l)

/-- `|∫_Σ Φ| ≤ M t^k/k!`. -/
lemma norm_simplexInt_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : ℝ} (hM : 0 ≤ M) (k : ℕ) :
    ∀ (t : ℝ) (Φ : List ℝ → E), 0 ≤ t → (∀ l : List ℝ, l.length = k → (∀ s ∈ l, 0 ≤ s ∧ s ≤ t) → ‖Φ l‖ ≤ M) →
      ‖simplexInt k t Φ‖ ≤ M * t ^ k / k.factorial := by
  induction k with
  | zero =>
    intro t Φ _ h
    simpa [simplexInt] using h [] rfl (by simp)
  | succ k ih =>
    intro t Φ ht h
    show ‖∫ s in (0 : ℝ)..t, simplexInt k s fun l => Φ (s :: l)‖ ≤ _
    have hb : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖simplexInt k s fun l => Φ (s :: l)‖ ≤ M * s ^ k / k.factorial := by
      intro s hs
      rw [uIoc_of_le ht] at hs
      refine ih s _ hs.1.le fun l hl hb => h (s :: l) (by simp [hl]) ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨hs.1.le, hs.2⟩
      · exact ⟨(hb x hx').1, (hb x hx').2.trans hs.2⟩
    refine (intervalIntegral.norm_integral_le_of_norm_le ht
      (Eventually.of_forall fun s hs => hb s (by rwa [uIoc_of_le ht])) ?_).trans (le_of_eq ?_)
    · exact (by fun_prop : Continuous fun s : ℝ => M * s ^ k / k.factorial).intervalIntegrable _ _
    · have hc : ∫ s in (0 : ℝ)..t, M * s ^ k / k.factorial = M / k.factorial * ∫ s in (0 : ℝ)..t, s ^ k := by
        rw [← intervalIntegral.integral_const_mul]; congr 1; funext s; ring
      rw [hc, integral_pow, Nat.factorial_succ]
      have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

section simplex

variable {a : L2H'}

lemma polyAct_mulP_cons (Q : WP) (p : ℂ × List Bool) (P : WP) :
    polyAct (mulP Q (p :: P)) a = p.1 • polyAct (mulP Q [(1, p.2)]) a + polyAct (mulP Q P) a := by
  induction Q with
  | nil => simp [mulP, polyAct]
  | cons q Q ih =>
    have e1 : mulP (q :: Q) (p :: P) = (q.1 * p.1, q.2 ++ p.2) :: ((P.map fun r => (q.1 * r.1, q.2 ++ r.2)) ++ mulP Q (p :: P)) := rfl
    have e2 : mulP (q :: Q) [(1, p.2)] = (q.1 * 1, q.2 ++ p.2) :: ([] ++ mulP Q [(1, p.2)]) := rfl
    have e3 : mulP (q :: Q) P = (P.map fun r => (q.1 * r.1, q.2 ++ r.2)) ++ mulP Q P := rfl
    rw [e1, e2, e3, polyAct_cons, polyAct_cons, polyAct_append, polyAct_append, polyAct_append, ih, smul_add, smul_smul]
    simp only [mul_one, List.nil_append, polyAct_nil, zero_add, smul_zero]
    rw [mul_comm p.1 q.1]
    abel

variable (hA : AllWords a) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E] (T : L2H' →ₗ[ℂ] E)

include hA

lemma polyAct_mulP_single (Q : WP) (w : List Bool) : polyAct (mulP Q [(1, w)]) a = polyAct Q (wordAct w a) := by
  rw [← polyAct_mulP hA]
  congr 1
  simp [polyAct]

/-- `T(Q(Σ p_i Z_{w_i} a)) = Σ p_i T(Q Z_{w_i} a)`. -/
lemma T_polyAct_expand (Q P : WP) :
    T (polyAct Q (polyAct P a)) = (P.map fun p => p.1 • T (polyAct Q (wordAct p.2 a))).sum := by
  rw [polyAct_mulP hA]
  induction P with
  | nil =>
    have : mulP Q [] = [] := by simp [mulP]
    rw [this]; simp [polyAct]
  | cons p P ih =>
    rw [polyAct_mulP_cons, polyAct_mulP_single hA, map_add, map_smul, ih]
    simp

omit hA in
lemma integral_list_sum {R : TP} (hR : Cont R) (y : List Bool → E) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (R.map fun r => r.1 s • y r.2).sum = (R.map fun r => (∫ s in (0 : ℝ)..t, r.1 s) • y r.2).sum := by
  induction R with
  | nil => simp
  | cons r R ih =>
    simp only [List.map_cons, List.sum_cons]
    have hc := hR r (by simp)
    have hR' : Cont R := fun q hq => hR q (by simp [hq])
    have c1 : Continuous fun s => r.1 s • y r.2 := hc.smul continuous_const
    have c2 : Continuous fun s => (R.map fun r => r.1 s • y r.2).sum := by
      clear ih
      induction R with
      | nil => simpa using continuous_const
      | cons q R ih2 =>
        simp only [List.map_cons, List.sum_cons]
        exact ((hR' q (by simp)).smul continuous_const).add
          (ih2 (fun x hx => hR x (by simp only [List.mem_cons] at hx ⊢; tauto)) fun x hx => hR' x (by simp [hx]))
    rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _), ih hR',
      intervalIntegral.integral_smul_const]

lemma integral_T_poly (Q : WP) {R : TP} (hR : Cont R) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, T (polyAct Q (polyAct (atT R s) a)) = T (polyAct Q (polyAct (atT (intTP R) t) a)) := by
  have e1 : ∀ s, T (polyAct Q (polyAct (atT R s) a))
      = (R.map fun r => r.1 s • T (polyAct Q (wordAct r.2 a))).sum := fun s => by
    rw [T_polyAct_expand hA, atT, List.map_map]; rfl
  simp_rw [e1]
  rw [integral_list_sum hR (fun w => T (polyAct Q (wordAct w a))) t, T_polyAct_expand hA, atT, intTP, List.map_map, List.map_map]
  rfl

/-- **The Dyson term as a simplex integral**, with a linear `T` on the left. -/
theorem simplex_poly (k : ℕ) : ∀ (Q : WP) (t : ℝ),
    simplexInt k t (fun l => T (polyAct Q (polyAct (deltaProd l) a))) = T (polyAct Q (xK a k t)) := by
  induction k with
  | zero =>
    intro Q t
    show T (polyAct Q (polyAct oneP a)) = _
    rw [polyAct_oneP, xK_zero]
  | succ k ih =>
    intro Q t
    show ∫ s in (0 : ℝ)..t, simplexInt k s (fun l => T (polyAct Q (polyAct (deltaProd (s :: l)) a))) = _
    have e : ∀ s, simplexInt k s (fun l => T (polyAct Q (polyAct (deltaProd (s :: l)) a)))
        = T (polyAct Q (polyAct (atT (mulTP deltaT (dysT k)) s) a)) := by
      intro s
      have hf : (fun l => T (polyAct Q (polyAct (deltaProd (s :: l)) a)))
          = fun l => T (polyAct (mulP Q (deltaP s)) (polyAct (deltaProd l) a)) := by
        funext l
        rw [polyAct_deltaProd_cons hA, polyAct_mulP (allWords_polyAct hA _)]
      have hx : AllWords (xK a k s) := allWords_polyAct hA _
      rw [hf, ih, ← poly_delta_xK hA, ← polyAct_mulP hx]
    simp_rw [e]
    exact integral_T_poly hA T Q (cont_mulTP cont_deltaT (cont_dysT k)) t

/-- `J_K(t)` as an integral over the simplex `Σ_{K+1}(t)`. -/
theorem jK_eq_simplex (hb : ℝ) (K : ℕ) (t : ℝ) :
    jK hb a K t = simplexInt (K + 1) t fun ss => dispVadj hb (ss.headD 0) (polyAct (deltaProd ss) a) := by
  show _ = ∫ s in (0 : ℝ)..t, simplexInt K s
    (fun l => dispVadj hb ((s :: l).headD 0) (polyAct (deltaProd (s :: l)) a))
  unfold jK
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hf : (fun l => dispVadj hb ((s :: l).headD 0) (polyAct (deltaProd (s :: l)) a))
      = fun l => dispVadjL hb s (polyAct (deltaP s) (polyAct (deltaProd l) a)) := by
    funext l
    rw [polyAct_deltaProd_cons hA]
    rfl
  show dispVadj hb s (polyAct (deltaP s) (xK a K s)) = _
  simp only [hf]
  rw [simplex_poly hA]
  rfl

/-- **(D1) + (D2), in the form used by `thm:dd-appx`**: with `c = iħ/2`,
`a - V(t)* a^{(K)}(t) = c^{K+1} ∫_{Σ_{K+1}(t)} V(s₁)* Δ(s₁)⋯Δ(s_{K+1}) a ds`. -/
theorem dd_D12_simplex {hb : ℝ} (hb0 : hb ≠ 0) (K : ℕ) (t : ℝ) :
    a - dispVadj hb t (∑ k ∈ Finset.range (K + 1), (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t)
      = (Complex.I * (hb : ℂ) / 2) ^ (K + 1)
        • simplexInt (K + 1) t fun ss => dispVadj hb (ss.headD 0) (polyAct (deltaProd ss) a) := by
  rw [dd_D12 hA hb0, jK_eq_simplex hA]

end simplex

end Qschubert
