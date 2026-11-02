import AcceleratedLogConcave.Conditional.JetBasics

/-! Analytic hypotheses for the complete flow, discharged from the original
C² convex potential by the proved Gaussian tilt regularity theorem. -/
noncomputable section
open Set Function
open scoped Topology

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def conditionalMeanSpatialDerivative (F : E → ℝ) (x : E) (r t : ℝ) (y : E) : E →L[ℝ] E :=
  (fderiv ℝ (fun p : ℝ × E => conditionalMean F x r p.1 p.2) (t, y)).comp
    (ContinuousLinearMap.inr ℝ ℝ E)

theorem continuousOn_conditionalMean {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    ContinuousOn (uncurry (conditionalMean F x r)) (Icc a b ×ˢ (univ : Set E)) :=
  (contDiffOn_conditionalMean hF hlo hup x r).continuousOn.mono
    (fun _ hp => ⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb⟩)

theorem continuousOn_conditionalMeanSpatialDerivative
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    ContinuousOn (uncurry (conditionalMeanSpatialDerivative F x r))
      (Icc a b ×ˢ (univ : Set E)) := by
  have hop : IsOpen {p : ℝ × E | -1 < p.1 ∧ p.1 < 1} := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  exact ((contDiffOn_conditionalMean hF hlo hup x r).continuousOn_fderiv_of_isOpen
    hop (by norm_num)).clm_comp continuousOn_const |>.mono
      (fun _ hp => ⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb⟩)

theorem hasFDerivAt_conditionalMeanSpatialDerivative
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {t : ℝ} (htlo : -1 < t) (hthi : t < 1) (y : E) :
    HasFDerivAt (conditionalMean F x r t) (conditionalMeanSpatialDerivative F x r t y) y := by
  have hop : IsOpen {p : ℝ × E | -1 < p.1 ∧ p.1 < 1} := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  have hj := (((contDiffOn_conditionalMean hF hlo hup x r) (t, y) ⟨htlo, hthi⟩).contDiffAt
    (hop.mem_nhds ⟨htlo, hthi⟩)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hc := hj.comp y ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id y))
  convert hc using 1 <;> rfl

end AcceleratedLogConcave.Conditional
