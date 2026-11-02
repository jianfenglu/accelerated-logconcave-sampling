import AcceleratedLogConcave.Analysis.SpatialVariationCalculus
import AcceleratedLogConcave.Conditional.Transport.JointFlowExtension

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialVariation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)

/-- A representative for the actual backward flow, not a surrogate flow. -/
theorem exists_smooth_backward_representative (hsmall : r^2*ell ≤ 1/2) (y : E) :
    ∃ C : ℝ × E → E, ContDiff ℝ ∞ C ∧
      ∀ t ∈ Icc 0 b, ∀ z ∈ ball y 1,
        C (t,z) = backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t z := by
  obtain ⟨S,hS,hSeq⟩ := exists_smooth_convexProbabilityFlow_extension
    hF hell hlo hup x hr hb hb1 hsmall y
  let C : ℝ × E → E := fun p => S ((b,p.1),p.2)
  have hC : ContDiff ℝ ∞ C :=
    hS.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  refine ⟨C,hC,?_⟩
  intro t ht z hz
  rw [backwardProbabilityTransport_eq_flow, projIcc_of_mem hb ht]
  exact hSeq ⟨b,hb,le_rfl⟩ ⟨t,ht⟩ z hz

/-- The zeroth-order ODE for the clipped public map, used only WITHIN its
closed construction slab. No differentiability of clipping is asserted. -/
theorem backward_hasDerivWithinAt {t : ℝ} (ht : t ∈ Icc 0 b) (y : E) :
    HasDerivWithinAt
      (fun s => backwardProbabilityTransport hF hell hlo hup x hr hb hb1 s y)
      (probabilityVelocity F x r t
        (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)) (Icc 0 b) t := by
  have he (s : ℝ) (hs : s ∈ Icc 0 b) :
      backwardProbabilityTransport hF hell hlo hup x hr hb hb1 s y =
        convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
          ⟨b,hb,le_rfl⟩ y s := by
    rw [backwardProbabilityTransport_eq_flow, projIcc_of_mem hb hs]
  have hd := convexProbabilityFlow_deriv hF hell hlo hup x hr hb (by norm_num) hb1
    ⟨b,hb,le_rfl⟩ y ht
  rw [← he t ht] at hd
  exact hd.congr_of_mem he ht

/-- ALL finite orders of actual INITIAL-DATA variation, on the full closed
slab. The RHS is the literal ordered spatial derivative of v_t ∘ Y_t.
It is deliberately NOT called a separated recurrence or a growth estimate. -/
theorem backward_spatial_variation (hsmall : r^2*ell ≤ 1/2)
    (J : List E) {t : ℝ} (ht : t ∈ Icc 0 b) (y : E) :
    HasDerivWithinAt
      (fun s => along J (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 s) y)
      (along J (fun z => probabilityVelocity F x r t
        (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t z)) y) (Icc 0 b) t := by
  obtain ⟨C,hC,hCY⟩ := exists_smooth_backward_representative
    hF hell hlo hup x hr hb hb1 hsmall y
  exact along_variation_of_local_representative hb hC y hCY
    (fun s hs z _ => backward_hasDerivWithinAt hF hell hlo hup x hr hb hb1 hs z) J ht

/-- Continuity of each literal spatial variation at BOTH time endpoints. -/
theorem backward_spatial_variation_continuousOn (hsmall : r^2*ell ≤ 1/2)
    (J : List E) (y : E) :
    ContinuousOn
      (fun s => along J (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 s) y)
      (Icc 0 b) :=
  fun _ ht => (backward_spatial_variation hF hell hlo hup x hr hb hb1 hsmall J ht y).continuousWithinAt

/-- Actual terminal spatial data, retained without a positive dimension or
positive terminal time assumption. -/
theorem backward_spatial_terminal (J : List E) (y : E) :
    along J (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 b) y =
      along J (id : E → E) y := by
  have he : (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 b : E → E) = id := by
    funext z
    have hz := backward_forwardProbabilityTransport hF hell hlo hup x hr hb hb1 b z
    simpa only [forwardProbabilityTransport_terminal, id_eq] using hz
  rw [he]

/-- The n=1 induction base is global and uniform on the slab (indeed for
every clipped time), with no polynomial coefficient hidden inside exp. -/
theorem norm_backward_fderiv_le (hsmall : r^2*ell ≤ 1/2) (t : ℝ) (y : E) :
    ‖fderiv ℝ (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t) y‖ ≤ Real.exp 1 := by
  exact norm_fderiv_le_of_lipschitz ℝ
    (lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1 hsmall
      ⟨b,hb,le_rfl⟩ (projIcc 0 b hb t))

/-- Uniform affine growth of the ACTUAL flow. Compactness is used only for
the single reference trajectory Y_t(0); initial-point growth is explicit. -/
theorem exists_backward_affine_envelope (hsmall : r^2*ell ≤ 1/2) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Icc 0 b, ∀ y : E,
      1 + ‖backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y‖ ≤ M * (1+‖y‖) := by
  have hc := backward_spatial_variation_continuousOn hF hell hlo hup x hr hb hb1
    hsmall [] (0:E)
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|A| + Real.exp 1 + 1, by positivity, ?_⟩
  intro t ht y
  have hbase : ‖backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t (0:E)‖ ≤ |A| :=
    (hA t ht).trans (le_abs_self A)
  have hd := (lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1
    hsmall ⟨b,hb,le_rfl⟩ (projIcc 0 b hb t)).dist_le_mul y (0:E)
  change dist (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)
    (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t (0:E)) ≤ Real.exp 1 * dist y 0 at hd
  rw [dist_eq_norm, dist_zero_right] at hd
  have hn := norm_le_norm_sub_add
    (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)
    (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t (0:E))
  nlinarith [norm_nonneg y, abs_nonneg A, Real.exp_pos 1]

theorem contDiff_backward_spatial (hsmall : r^2*ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ContDiff ℝ ∞ (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t : E → E) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  obtain ⟨C,hC,hCY⟩ := exists_smooth_backward_representative
    hF hell hlo hup x hr hb hb1 hsmall y
  have hs : ContDiff ℝ ∞ (fun z => C (t,z)) := hC.comp (contDiff_const.prodMk contDiff_id)
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
  exact (hCY t ht z hz).symm

include hF hlo hup in
theorem contDiff_probabilityVelocity_spatial {t : ℝ} (htlo : -1 < t) (hthi : t < 1) :
    ContDiff ℝ ∞ (probabilityVelocity F x r t) := by
  have hs := (contDiffOn_conditionalMean hF hlo hup x r).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (s := Set.univ)
    (fun _ _ => And.intro htlo hthi)
  exact (contDiffOn_univ.mp hs).const_smul (-r)

/-- The same all-order variational equation expressed using the literal
iterated Frechet derivative evaluated on an arbitrary direction tuple. -/
theorem backward_iteratedFDeriv_variation (hsmall : r^2*ell ≤ 1/2)
    (n : ℕ) (m : Fin n → E) {t : ℝ} (ht : t ∈ Icc 0 b) (y : E) :
    HasDerivWithinAt
      (fun s => iteratedFDeriv ℝ n
        (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 s) y m)
      (iteratedFDeriv ℝ n (fun z => probabilityVelocity F x r t
        (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t z)) y m) (Icc 0 b) t := by
  have h := backward_spatial_variation hF hell hlo hup x hr hb hb1 hsmall (List.ofFn m) ht y
  have hY := contDiff_backward_spatial hF hell hlo hup x hr hb hb1 hsmall ht
  have hV := contDiff_probabilityVelocity_spatial hF hlo hup x (r := r)
    (by linarith [ht.1]) (ht.2.trans_lt hb1)
  have he := along_ofFn_eq_iteratedFDeriv (hV.comp hY) n m y
  dsimp only [Function.comp_def] at he
  rw [he] at h
  exact h.congr_of_mem (fun s hs =>
    (along_ofFn_eq_iteratedFDeriv
      (contDiff_backward_spatial hF hell hlo hup x hr hb hb1 hsmall hs) n m y).symm) ht

/-- The n=2 actual spatial ODE with the highest variation SEPARATED LINEARLY.
The second summand has only first spatial variations of Y, not its second
variation. The two directions may coincide or be zero. -/
theorem backward_second_spatial_variation (hsmall : r^2*ell ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc 0 b) (y v w : E) :
    HasDerivWithinAt
      (fun s => along [v,w] (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 s) y)
      (fderiv ℝ (probabilityVelocity F x r t)
          (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)
          (along [v,w] (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t) y) +
        (fderiv ℝ (fderiv ℝ (probabilityVelocity F x r t))
          (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)
          (fderiv ℝ (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t) y v))
          (fderiv ℝ (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t) y w))
      (Icc 0 b) t := by
  have h := backward_spatial_variation hF hell hlo hup x hr hb hb1 hsmall [v,w] ht y
  rw [second_composition_split
    (contDiff_probabilityVelocity_spatial hF hlo hup x (r := r)
      (by linarith [ht.1]) (ht.2.trans_lt hb1))
    (contDiff_backward_spatial hF hell hlo hup x hr hb hb1 hsmall ht)] at h
  exact h

theorem backward_second_spatial_terminal (y v w : E) :
    along [v,w] (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 b) y = 0 := by
  rw [backward_spatial_terminal hF hell hlo hup x hr hb hb1]
  simp only [along, fderiv_id, ContinuousLinearMap.id_apply, fderiv_const_apply, zero_apply]

/-- Every spatial order at least two has zero terminal data. -/
theorem backward_higher_spatial_terminal (y v w : E) (J : List E) :
    along (v :: w :: J) (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 b) y = 0 := by
  rw [backward_spatial_terminal hF hell hlo hup x hr hb hb1, along_id_at_least_two]

/-- The actual coefficient of the top-order variation is bounded independently
of the initial spatial point. This is the coefficient allowed in Gronwall. -/
theorem norm_backward_variation_coefficient_le {t : ℝ} (ht : t ∈ Icc 0 b) (y : E) :
    ‖fderiv ℝ (probabilityVelocity F x r t)
      (backwardProbabilityTransport hF hell hlo hup x hr hb hb1 t y)‖ ≤ r^2*ell := by
  exact norm_fderiv_le_of_lipschitz ℝ
    (lipschitzWith_probabilityVelocity hF hell hlo hup x hr
      (by linarith [ht.1]) (ht.2.trans_lt hb1))

end AcceleratedLogConcave.Conditional.Transport.SpatialFlow
