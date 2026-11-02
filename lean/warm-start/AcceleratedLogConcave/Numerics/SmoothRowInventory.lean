import AcceleratedLogConcave.Numerics.SmoothRowPayments

/-! An inventory-independent scalar majorant for the explicit physical row
coefficients. Local variances and trigonometric factors are bounded here,
without counting nodes or replacing a signed output by another sampler. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SmoothRowInventory
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly SmoothQuadraturePayments SmoothRowPayments
open ConditionalSmoothing
variable {D m : ℕ}

def positionBound (d : Data (Fin D) m) : ℝ :=
  stateCoefficient d + SmoothAnglePayment.velocityCoefficient d

def backwardBound (d : Data (Fin D) m) : ℝ := positionBound d + d.r*
  (2^(m+1)*backwardEnd d.G.R*materialBackwardDerivativeBudget d (m-1)/(m.factorial:ℝ))

def conditionalBound (d : Data (Fin D) m) : ℝ :=
  2^(m+1)*conditionalEnd*d.ell*d.r^2*
    Real.sqrt (Fintype.card (Fin D))*conditionalOrderEnvelope m/(m.factorial:ℝ)

def forwardBound (d : Data (Fin D) m) : ℝ :=
  2^(m+1)*backwardEnd d.G.R*forwardDerivativeBudget d m/(m.factorial:ℝ)

def inventoryBound (d : Data (Fin D) m) : ℝ :=
  3*backwardBound d+4*conditionalBound d+scoreCoefficient d+d.r*forwardBound d

theorem positionBound_nonneg (d : Data (Fin D) m) : 0 ≤ positionBound d := by
  unfold positionBound stateCoefficient
  have := d.G.R_pos.le
  have := SmoothAnglePayment.velocityCoefficient_nonneg d
  positivity

theorem backwardBound_nonneg (d : Data (Fin D) m) : 0 ≤ backwardBound d := by
  unfold backwardBound
  have := positionBound_nonneg d
  have := d.hr.le
  have := d.G.backwardEnd_pos.le
  have := materialBackwardDerivativeBudget_nonneg d (m-1)
  positivity

theorem conditionalBound_nonneg (d : Data (Fin D) m) : 0 ≤ conditionalBound d := by
  unfold conditionalBound
  have := d.hell
  have := conditionalOrderEnvelope_nonneg m
  have : 0 ≤ conditionalEnd := by norm_num [conditionalEnd]
  positivity

theorem forwardBound_nonneg (d : Data (Fin D) m) : 0 ≤ forwardBound d := by
  unfold forwardBound
  have := d.G.backwardEnd_pos.le
  have := forwardDerivativeBudget_nonneg d m
  positivity

theorem scoreCoefficient_nonneg (d : Data (Fin D) m) : 0 ≤ scoreCoefficient d := by
  unfold scoreCoefficient
  have := centerCoefficient_nonneg d
  have := d.hsigma.le
  positivity

theorem inventoryBound_nonneg (d : Data (Fin D) m) : 0 ≤ inventoryBound d := by
  unfold inventoryBound
  have := backwardBound_nonneg d
  have := conditionalBound_nonneg d
  have := scoreCoefficient_nonneg d
  have := forwardBound_nonneg d
  have := d.hr.le
  positivity

theorem positionCoefficient_le (d : Data (Fin D) m) (hm : 0 < m) {a : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) : positionCoefficient d a ≤ positionBound d := by
  have hsum := sum_abs_centerRow_le m hm a ha
  unfold positionCoefficient positionBound
  rw [← Finset.sum_mul]
  have h := mul_le_mul_of_nonneg_right hsum (SmoothAnglePayment.velocityCoefficient_nonneg d)
  simpa only [one_mul] using add_le_add_right h (stateCoefficient d)

theorem backwardCoefficient_le (d : Data (Fin D) m) (hm : 0 < m) (j : Fin m) :
    backwardCoefficient d j ≤ backwardBound d :=
  add_le_add_left (positionCoefficient_le d hm ⟨(centerNode_mem j).1.le, (centerNode_mem j).2.le⟩) _

theorem variance_le_one (d : Data (Fin D) m) (ρ : d.G.Kernel) : d.G.variance ρ ≤ 1 := by
  unfold variance
  nlinarith [sq_nonneg (d.G.rho ρ)]

theorem sqrt_variance_le_one (d : Data (Fin D) m) (ρ : d.G.Kernel) :
    Real.sqrt (d.G.variance ρ) ≤ 1 :=
  (Real.sqrt_le_sqrt (variance_le_one d ρ)).trans_eq Real.sqrt_one

theorem conditionalCoefficient_le (d : Data (Fin D) m) (ρ : d.G.Kernel) :
    conditionalCoefficient d ρ ≤ conditionalBound d := by
  have h := mul_le_mul_of_nonneg_left (variance_le_one d ρ) (conditionalBound_nonneg d)
  convert h using 1 <;> simp only [conditionalCoefficient, conditionalBound] <;> ring

theorem forwardCoefficient_le (d : Data (Fin D) m) (ρ : d.G.Kernel) :
    forwardCoefficient d ρ ≤ forwardBound d := by
  unfold forwardCoefficient forwardBound
  have hf := forwardDerivativeBudget_nonneg d m
  gcongr
  linarith [(d.G.rho_mem ρ).1]

theorem rotationScale_le_one (d : Data (Fin D) m) (ρ : d.G.Kernel) :
    d.G.rotationScale ρ ≤ 1 := by
  have hv := variance_le_one d ρ
  have hs := d.G.rotationScale_sq ρ
  have hd : (0:ℝ) < 1+(d.G.rho ρ)^2 := by positivity
  have hdiv : d.G.variance ρ/(1+(d.G.rho ρ)^2) ≤ 1 :=
    (div_le_one₀ hd).mpr (by nlinarith [sq_nonneg (d.G.rho ρ)])
  nlinarith [d.G.rotationScale_pos ρ]

theorem rotation_weights (d : Data (Fin D) m) (ρ : d.G.Kernel) (z : ℝ) :
    |1-(d.G.rotationScale ρ)^2*(1-Real.cos (z/d.G.rotationScale ρ))| ≤ 3 ∧
    |d.G.rho ρ * Real.sqrt (d.G.variance ρ)/(conditionalEnd*(1+(d.G.rho ρ)^2))*
      (1-Real.cos (z/d.G.rotationScale ρ))| ≤ 4 ∧
    |d.G.rotationScale ρ*Real.sin (z/d.G.rotationScale ρ)| ≤ 1 := by
  have hs0 := (d.G.rotationScale_pos ρ).le
  have hs1 := rotationScale_le_one d ρ
  have hc0 := Real.neg_one_le_cos (z/d.G.rotationScale ρ)
  have hc1 := Real.cos_le_one (z/d.G.rotationScale ρ)
  have hsp : (d.G.rotationScale ρ)^2 ≤ 1 := by nlinarith
  have hprod : 0 ≤ (d.G.rotationScale ρ)^2*(1-Real.cos (z/d.G.rotationScale ρ)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hprod2 : (d.G.rotationScale ρ)^2*(1-Real.cos (z/d.G.rotationScale ρ)) ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsp) (show 0 ≤ 1-Real.cos (z/d.G.rotationScale ρ) by linarith)]
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · have hr0 := (d.G.rho_mem ρ).1
    have hr1 := ((d.G.rho_mem ρ).2.trans d.G.backwardEnd_lt_one).le
    have hv0 := Real.sqrt_nonneg (d.G.variance ρ)
    have hv1 := sqrt_variance_le_one d ρ
    have hn : d.G.rho ρ*Real.sqrt (d.G.variance ρ) ≤ 1 := by nlinarith
    have hd : (0:ℝ) < conditionalEnd*(1+(d.G.rho ρ)^2) := by norm_num [conditionalEnd]; positivity
    have hquot0 : 0 ≤ d.G.rho ρ*Real.sqrt (d.G.variance ρ)/(conditionalEnd*(1+(d.G.rho ρ)^2)) :=
      div_nonneg (mul_nonneg hr0 hv0) hd.le
    have hquot2 : d.G.rho ρ*Real.sqrt (d.G.variance ρ)/(conditionalEnd*(1+(d.G.rho ρ)^2)) ≤ 2 := by
      apply (div_le_iff₀ hd).mpr
      have he : conditionalEnd^2 = (1:ℝ)/2 := by norm_num [conditionalEnd, Real.sq_sqrt]
      have he0 := conditionalEnd_pos
      have hhalf : (1:ℝ)/2 ≤ conditionalEnd := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (d.G.rho ρ)) conditionalEnd_pos.le]
    rw [abs_of_nonneg (mul_nonneg hquot0 (by linarith))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hquot2) (show 0 ≤ 1-Real.cos (z/d.G.rotationScale ρ) by linarith)]
  · rw [abs_mul, abs_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) hs0).trans (by simpa using hs1)

theorem positionCoefficient_nonneg (d : Data (Fin D) m) (a : ℝ) :
    0 ≤ positionCoefficient d a := by
  unfold positionCoefficient stateCoefficient
  have := SmoothAnglePayment.velocityCoefficient_nonneg d
  have := d.G.R_pos.le
  positivity

theorem backwardCoefficient_nonneg (d : Data (Fin D) m) (j : Fin m) :
    0 ≤ backwardCoefficient d j := by
  unfold backwardCoefficient
  have := positionCoefficient_nonneg d (centerNode j)
  have := d.hr.le
  have := d.G.backwardEnd_pos.le
  have := materialBackwardDerivativeBudget_nonneg d (m-1)
  positivity

theorem conditionalCoefficient_nonneg (d : Data (Fin D) m) (ρ : d.G.Kernel) :
    0 ≤ conditionalCoefficient d ρ := by
  have he : conditionalCoefficient d ρ = conditionalBound d*d.G.variance ρ := by
    unfold conditionalCoefficient conditionalBound
    ring
  rw [he]
  exact mul_nonneg (conditionalBound_nonneg d) (d.G.variance_pos ρ).le

theorem forwardCoefficient_nonneg (d : Data (Fin D) m) (ρ : d.G.Kernel) :
    0 ≤ forwardCoefficient d ρ := by
  unfold forwardCoefficient
  have := sub_nonneg.mpr (d.G.rho_mem ρ).2.le
  have := forwardDerivativeBudget_nonneg d m
  positivity

theorem rotationCoefficient_nonneg (d : Data (Fin D) m) (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) :
    0 ≤ rotationCoefficient d j ρ z := by
  unfold rotationCoefficient
  have := backwardCoefficient_nonneg d j
  have := conditionalCoefficient_nonneg d ρ
  have := scoreCoefficient_nonneg d
  positivity

theorem rotationCoefficient_le (d : Data (Fin D) m) (hm : 0 < m)
    (j : Fin m) (ρ : d.G.Kernel) (z : ℝ) :
    rotationCoefficient d j ρ z ≤ 3*backwardBound d+4*conditionalBound d+scoreCoefficient d := by
  have hw := rotation_weights d ρ z
  unfold rotationCoefficient
  apply add_le_add
  · exact add_le_add
      (mul_le_mul hw.1 (backwardCoefficient_le d hm j)
        (backwardCoefficient_nonneg d j) (by norm_num))
      (mul_le_mul hw.2.1 (conditionalCoefficient_le d ρ)
        (conditionalCoefficient_nonneg d ρ) (by norm_num))
  · exact (mul_le_mul_of_nonneg_right hw.2.2 (scoreCoefficient_nonneg d)).trans_eq (one_mul _)

theorem rowCoefficient_nonneg (d : Data (Fin D) m) (i : d.G.MeanNode) :
    0 ≤ rowCoefficient d i := by
  have hr := d.hr.le
  rcases i with ⟨⟩ | j | ⟨j,k⟩ | ⟨j,ρ,k⟩ | ⟨j,ρ,z,k⟩
  · rfl
  · exact mul_nonneg (mul_nonneg hr d.G.backwardEnd_pos.le) (positionCoefficient_nonneg d _)
  · exact mul_nonneg (mul_nonneg hr (d.G.backward.location_mem_interval m k).1.le)
      (backwardCoefficient_nonneg d j)
  · exact add_nonneg
      (mul_nonneg (mul_nonneg hr (d.G.rho_mem ρ).1) (backwardCoefficient_nonneg d j))
      (mul_nonneg (mul_nonneg (mul_nonneg hr (Real.sqrt_nonneg _))
        ((d.G.conditional ρ).location_mem_interval m k).1.le) (conditionalCoefficient_nonneg d ρ))
  · exact mul_nonneg (mul_nonneg hr ((d.G.rho_mem ρ).1.trans
      ((d.G.forward ρ).location_mem_interval m k).1.le))
      (add_nonneg (rotationCoefficient_nonneg d j ρ _) (mul_nonneg hr (forwardCoefficient_nonneg d ρ)))

/-- The coefficient inventory has a scalar majorant independent of its number
of nodes, and its outer physical radius is preserved. -/
theorem rowCoefficient_le (d : Data (Fin D) m) (hm : 0 < m) (i : d.G.MeanNode) :
    rowCoefficient d i ≤ d.r*inventoryBound d := by
  have hr := d.hr.le
  have hB := backwardBound_nonneg d
  have hC := conditionalBound_nonneg d
  have hS := scoreCoefficient_nonneg d
  have hF := forwardBound_nonneg d
  have hPB : positionBound d ≤ backwardBound d := by
    unfold backwardBound
    have := materialBackwardDerivativeBudget_nonneg d (m-1)
    have := d.G.backwardEnd_pos.le
    apply le_add_of_nonneg_right
    positivity
  have hBA : backwardBound d ≤ inventoryBound d := by unfold inventoryBound; nlinarith
  have hBCA : backwardBound d+conditionalBound d ≤ inventoryBound d := by
    unfold inventoryBound; nlinarith
  rcases i with ⟨⟩ | j | ⟨j,k⟩ | ⟨j,ρ,k⟩ | ⟨j,ρ,z,k⟩
  · exact mul_nonneg hr (inventoryBound_nonneg d)
  · change d.r*backwardEnd d.G.R*positionCoefficient d (centerNode j) ≤ _
    calc
      _ ≤ d.r*backwardEnd d.G.R*backwardBound d := mul_le_mul_of_nonneg_left
        ((positionCoefficient_le d hm ⟨(centerNode_mem j).1.le, (centerNode_mem j).2.le⟩).trans hPB)
        (mul_nonneg hr d.G.backwardEnd_pos.le)
      _ ≤ d.r*backwardBound d := by
        have h := mul_le_mul_of_nonneg_left d.G.backwardEnd_lt_one.le (mul_nonneg hr hB)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hBA hr
  · change d.r*d.G.backward.location m k*backwardCoefficient d j ≤ _
    have ha := d.G.backward.location_mem_interval m k
    calc
      _ ≤ d.r*d.G.backward.location m k*backwardBound d :=
        mul_le_mul_of_nonneg_left (backwardCoefficient_le d hm j) (mul_nonneg hr ha.1.le)
      _ ≤ d.r*backwardBound d := by
        have h := mul_le_mul_of_nonneg_left (ha.2.trans d.G.backwardEnd_lt_one).le (mul_nonneg hr hB)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hBA hr
  · change d.r*d.G.rho ρ*backwardCoefficient d j +
      d.r*Real.sqrt (d.G.variance ρ)*(d.G.conditional ρ).location m k*conditionalCoefficient d ρ ≤ _
    have hv0 := Real.sqrt_nonneg (d.G.variance ρ)
    have hv1 := sqrt_variance_le_one d ρ
    have ha := (d.G.conditional ρ).location_mem_interval m k
    have ha1 : (d.G.conditional ρ).location m k ≤ 1 := by
      exact (ha.2.trans conditionalEnd_lt_one).le
    have hab : Real.sqrt (d.G.variance ρ)*(d.G.conditional ρ).location m k ≤ 1 := by nlinarith
    have hleft := mul_le_mul_of_nonneg_left (backwardCoefficient_le d hm j)
      (mul_nonneg hr (d.G.rho_mem ρ).1)
    have hright := mul_le_mul_of_nonneg_left (conditionalCoefficient_le d ρ)
      (mul_nonneg (mul_nonneg hr hv0) ha.1.le)
    have hrho := ((d.G.rho_mem ρ).2.trans d.G.backwardEnd_lt_one).le
    have hbr := mul_le_mul_of_nonneg_left hrho (mul_nonneg hr hB)
    have hcr := mul_le_mul_of_nonneg_left hab (mul_nonneg hr hC)
    have hout := mul_le_mul_of_nonneg_left hBCA hr
    nlinarith
  · change d.r*(d.G.forward ρ).location m k*
      (rotationCoefficient d j ρ (d.G.angleNode z)+d.r*forwardCoefficient d ρ) ≤ _
    have ha := (d.G.forward ρ).location_mem_interval m k
    have ha0 := (d.G.rho_mem ρ).1.trans ha.1.le
    have hinside := add_le_add (rotationCoefficient_le d hm j ρ (d.G.angleNode z))
      (mul_le_mul_of_nonneg_left (forwardCoefficient_le d ρ) hr)
    have hscale := mul_le_mul_of_nonneg_left hinside (mul_nonneg hr ha0)
    change d.r*(d.G.forward ρ).location m k*(rotationCoefficient d j ρ (d.G.angleNode z)+d.r*forwardCoefficient d ρ) ≤
      d.r*(d.G.forward ρ).location m k*inventoryBound d at hscale
    apply hscale.trans
    have := mul_le_mul_of_nonneg_left (ha.2.trans d.G.backwardEnd_lt_one).le
      (mul_nonneg hr (inventoryBound_nonneg d))
    nlinarith

theorem norm_rowCoefficient_le (d : Data (Fin D) m) (hm : 0 < m) :
    ‖rowCoefficient d‖ ≤ d.r*inventoryBound d := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg d.hr.le (inventoryBound_nonneg d))).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (rowCoefficient_nonneg d i)]
  exact rowCoefficient_le d hm i

end AcceleratedLogConcave.Numerics.SmoothRowInventory
