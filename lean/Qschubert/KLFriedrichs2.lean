import Qschubert.Friedrichs
import Qschubert.Evolution

/-!
# Unitary equivalence: Friedrichs extensions and propagators

`FriedrichsNat.lean` treats a unitary of one Hilbert space. Here `U : H ≃ₗᵢ H'` goes between two spaces, as for the map
`L²(M') → L²(M)` of conjugate groups.

* `IntertwinesOp T T' U`: `U` maps `Dom T` into `Dom T'` and `T' U = U T` there;
* `friedrichsExt_U2`: then the Friedrichs extensions are intertwined too;
* `evol_intertwine`: unitaries intertwining the generators intertwine the propagators.
-/

namespace Qschubert

open Physicslib4.Spectral.Unbounded
open scoped InnerProductSpace

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- `U` maps `Dom T` into `Dom T'` and `T' U = U T`. -/
structure IntertwinesOp (T : H →ₗ.[ℂ] H) (T' : H' →ₗ.[ℂ] H') (U : H ≃ₗᵢ[ℂ] H') : Prop where
  mem : ∀ x ∈ T.domain, U x ∈ T'.domain
  comm : ∀ (x : T.domain) (hx : U x ∈ T'.domain), T' ⟨U x, hx⟩ = U (T x)

variable (T : H →ₗ.[ℂ] H) (T' : H' →ₗ.[ℂ] H') [hT : Fact (IsPositive T)] [hT' : Fact (IsPositive T')]
  {U : H ≃ₗᵢ[ℂ] H'}

namespace FormDom

/-- `U` on the form domains. -/
noncomputable def mapU2 (hU : IntertwinesOp T T' U) : FormDom T →ₗ[ℂ] FormDom T' where
  toFun x := ofDom T' ⟨U (val T x), hU.mem _ (toDom T x).2⟩
  map_add' x y := by
    apply Subtype.ext
    show U (val T (x + y)) = U (val T x) + U (val T y)
    rw [val_add, map_add]
  map_smul' c x := by
    apply Subtype.ext
    show U (val T (c • x)) = c • U (val T x)
    rw [val_smul, map_smul]

lemma val_mapU2 (hU : IntertwinesOp T T' U) (x : FormDom T) : val T' (mapU2 T T' hU x) = U (val T x) := rfl

lemma app_mapU2 (hU : IntertwinesOp T T' U) (x : FormDom T) : app T' (mapU2 T T' hU x) = U (app T x) :=
  hU.comm (toDom T x) _

lemma inner_mapU2 (hU : IntertwinesOp T T' U) (x y : FormDom T) :
    ⟪mapU2 T T' hU x, mapU2 T T' hU y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_eq, inner_eq, formInner, formInner, val_mapU2, val_mapU2, app_mapU2,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

lemma norm_mapU2 (hU : IntertwinesOp T T' U) (x : FormDom T) : ‖mapU2 T T' hU x‖ = ‖x‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_mapU2]

/-- `U` on the form domains, continuous. -/
noncomputable def mapUL2 (hU : IntertwinesOp T T' U) : FormDom T →L[ℂ] FormDom T' :=
  LinearMap.mkContinuous (mapU2 T T' hU) 1 (fun x => by rw [norm_mapU2, one_mul])

end FormDom

/-- `U` on the form spaces. -/
noncomputable def formU2 (hU : IntertwinesOp T T' U) : FormSpace T →L[ℂ] FormSpace T' :=
  ((UniformSpace.Completion.toComplL : FormDom T' →L[ℂ] FormSpace T').comp (FormDom.mapUL2 T T' hU)).extend
    (UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T)

lemma formU2_coe (hU : IntertwinesOp T T' U) (x : FormDom T) :
    formU2 T T' hU (x : FormSpace T) = ((FormDom.mapU2 T T' hU x : FormDom T') : FormSpace T') :=
  ContinuousLinearMap.extend_eq _ (e := (UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T))
    UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _) x

lemma inner_formU2 (hU : IntertwinesOp T T' U) (u w : FormSpace T) :
    ⟪formU2 T T' hU u, formU2 T T' hU w⟫_ℂ = ⟪u, w⟫_ℂ := by
  refine UniformSpace.Completion.induction_on₂ u w ?_ ?_
  · exact isClosed_eq (((formU2 T T' hU).continuous.comp continuous_fst).inner
      ((formU2 T T' hU).continuous.comp continuous_snd)) (continuous_fst.inner continuous_snd)
  · intro x y
    rw [formU2_coe, formU2_coe, UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
      FormDom.inner_mapU2]

lemma formIncl_formU2 (hU : IntertwinesOp T T' U) (u : FormSpace T) :
    formIncl T' (formU2 T T' hU u) = U (formIncl T u) := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · exact isClosed_eq ((formIncl T').continuous.comp (formU2 T T' hU).continuous)
      (U.continuous.comp (formIncl T).continuous)
  · intro x
    rw [formU2_coe, formIncl_coe, formIncl_coe, FormDom.val_mapU2]

lemma formU2_symm (hU : IntertwinesOp T T' U) (hU' : IntertwinesOp T' T U.symm) (w : FormSpace T') :
    formU2 T T' hU (formU2 T' T hU' w) = w := by
  refine UniformSpace.Completion.induction_on w ?_ ?_
  · exact isClosed_eq ((formU2 T T' hU).continuous.comp (formU2 T' T hU').continuous) continuous_id
  · intro x
    rw [formU2_coe, formU2_coe]
    congr 1
    apply Subtype.ext
    show U (U.symm (FormDom.val T' x)) = FormDom.val T' x
    simp

lemma adjoint_formIncl_U2 (hU : IntertwinesOp T T' U) (hU' : IntertwinesOp T' T U.symm) (f : H) :
    ContinuousLinearMap.adjoint (formIncl T') (U f)
      = formU2 T T' hU (ContinuousLinearMap.adjoint (formIncl T) f) := by
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  conv_rhs => rw [← formU2_symm T T' hU hU' w, inner_formU2, ContinuousLinearMap.adjoint_inner_left,
    formIncl_formU2]
  rw [← LinearIsometryEquiv.inner_map_map U f, LinearIsometryEquiv.apply_symm_apply]

/-- `R' U = U R`. -/
theorem formRes_U2 (hU : IntertwinesOp T T' U) (hU' : IntertwinesOp T' T U.symm) (f : H) :
    formRes T' (U f) = U (formRes T f) := by
  rw [formRes, ContinuousLinearMap.comp_apply, adjoint_formIncl_U2 T T' hU hU', formIncl_formU2]
  rfl

/-- **Friedrichs extensions are unitarily natural, between two spaces.** -/
theorem friedrichsExt_U2 (hd : HasDenseDomain T) (hd' : HasDenseDomain T') (hU : IntertwinesOp T T' U)
    (hU' : IntertwinesOp T' T U.symm) (x : (friedrichsExt T hd).domain) :
    ∃ h : U x ∈ (friedrichsExt T' hd').domain, friedrichsExt T' hd' ⟨U x, h⟩ = U (friedrichsExt T hd x) := by
  obtain ⟨g, rfl⟩ := (resEquiv T hd).surjective x
  have hmem : U (resEquiv T hd g : H) ∈ (friedrichsExt T' hd').domain :=
    ⟨U g, by rw [coe_resEquiv]; exact formRes_U2 T T' hU hU' g⟩
  refine ⟨hmem, ?_⟩
  have heq : (⟨U (resEquiv T hd g : H), hmem⟩ : (friedrichsExt T' hd').domain) = resEquiv T' hd' (U g) :=
    Subtype.ext (show U (formRes T g) = formRes T' (U g) from (formRes_U2 T T' hU hU' g).symm)
  rw [heq, friedrichsExt_apply, friedrichsExt_apply, formRes_U2 T T' hU hU', map_sub]

/-- **Intertwining the generators intertwines the propagators.** -/
theorem evol_intertwine {A : H →ₗ.[ℂ] H} {A' : H' →ₗ.[ℂ] H'} (hA : IsSelfAdjoint A) (hA' : IsSelfAdjoint A')
    (S : H →L[ℂ] H') (hS : ∀ (v : H) (hv : v ∈ A.domain), ∃ h : S v ∈ A'.domain, A' ⟨S v, h⟩ = S (A ⟨v, hv⟩))
    (hb t : ℝ) (v : H) : S (evol hA hb t v) = evol hA' hb t (S v) := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hdr : DenseRange (fun x : A.domain => (x : H)) := hdense.denseRange_val
  refine hdr.induction_on v ?_ fun x => ?_
  · exact isClosed_eq (S.continuous.comp (evol hA hb t).continuous)
      ((evol hA' hb t).continuous.comp S.continuous)
  · have hx : (x : H) ∈ A.domain := x.2
    set w₁ : ℝ → H' := fun r => S (evol hA hb r (x : H)) with hw₁
    have hdom : ∀ s, w₁ s ∈ A'.domain := fun s => (hS _ (A_evol hA hb s _ hx).1).1
    have hder : ∀ s, HasDerivAt (fun r => evol hA' hb (-r) (w₁ r)) 0 s := fun s => by
      have h1 : HasDerivAt w₁ (S ((-(Complex.I * (hb : ℂ) / 2)) • evol hA hb s (A ⟨x, hx⟩))) s :=
        ((S.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt s (hasDerivAt_evol hA hb s _ hx)
      have h2 := hasDerivAt_evol_neg_comp hA' hb h1 (hdom s)
      obtain ⟨hm, e⟩ := A_evol hA hb s _ hx
      obtain ⟨hm', e'⟩ := hS _ hm
      have e2 : A' ⟨w₁ s, hdom s⟩ = S (evol hA hb s (A ⟨x, hx⟩)) := by rw [← e]; exact e'
      have e3 : S ((-(Complex.I * (hb : ℂ) / 2)) • evol hA hb s (A ⟨x, hx⟩))
          + (Complex.I * (hb : ℂ) / 2) • A' ⟨w₁ s, hdom s⟩ = 0 := by
        rw [e2, map_smul, _root_.neg_smul, neg_add_cancel]
      rw [e3, map_zero] at h2
      exact h2
    have hconst := is_const_of_deriv_eq_zero (f := fun r => evol hA' hb (-r) (w₁ r))
      (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) t 0
    have h0 : evol hA' hb (-0) (w₁ 0) = S (x : H) := by
      simp only [neg_zero, hw₁, evol_zero, ContinuousLinearMap.one_apply]
    have hU : evol hA' hb t (evol hA' hb (-t) (w₁ t)) = w₁ t := by
      have h := evol_add hA' hb t (-t)
      rw [add_neg_cancel, evol_zero] at h
      exact (congrArg (fun R => R (w₁ t)) h).symm
    show S (evol hA hb t (x : H)) = evol hA' hb t (S (x : H))
    rw [← h0, ← hconst, hU]

end Qschubert
