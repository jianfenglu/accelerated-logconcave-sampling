import AcceleratedLogConcave.Oracle.RecursiveCallRatio

/-! Sufficient scalar size bounds for one recursive call. These are explicit
inequalities, not desired-output certificates or a reachable-call invariant. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveSize
open Numerics.AffineGraph RecursiveCallAccounting

def SizeBound (lam δ b s r σ : ℝ) : Prop :=
  lam*r^2 ≤ s*δ ^ b ∧ lam*(r/σ) ≤ s*δ ^ b

def mainFactor (B : ℝ) : ℝ := 4*Real.sqrt 5*B
def rowFactor (m : ℕ) : ℝ := 256*(m:ℝ)^5+4
def stepFactor (m : ℕ) (B : ℝ) : ℝ := 3+mainFactor B*rowFactor m

theorem mainFactor_ge_one (B : ℝ) (hB : 1 ≤ B) : 1 ≤ mainFactor B := by
  have hs : (1:ℝ) ≤ Real.sqrt 5 := Real.le_sqrt_of_sq_le (by norm_num)
  unfold mainFactor
  nlinarith

theorem rowFactor_ge_one (m : ℕ) : 1 ≤ rowFactor m := by
  unfold rowFactor
  have h : 0 ≤ 256*(m:ℝ)^5 := by positivity
  linarith

theorem stepFactor_ge_three (m : ℕ) (B : ℝ) (hB : 0 ≤ B) : 3 ≤ stepFactor m B := by
  unfold stepFactor
  exact le_add_of_nonneg_right (mul_nonneg (by unfold mainFactor; positivity)
    (le_trans (by norm_num) (rowFactor_ge_one m)))

theorem stepFactor_ge_product (m : ℕ) (B : ℝ) :
    mainFactor B*rowFactor m ≤ stepFactor m B := by unfold stepFactor; linarith

theorem stepFactor_ge_main (m : ℕ) (B : ℝ) (hB : 1 ≤ B) : mainFactor B ≤ stepFactor m B := by
  calc
    mainFactor B ≤ mainFactor B*rowFactor m :=
      le_mul_of_one_le_right (le_trans (by norm_num) (mainFactor_ge_one B hB))
        (rowFactor_ge_one m)
    _ ≤ _ := stepFactor_ge_product m B

theorem SizeBound.zero (δ b s r σ : ℝ) (hδ : 0 < δ) (hs : 0 ≤ s) :
    SizeBound 0 δ b s r σ := by
  constructor <;> simpa using mul_nonneg hs (Real.rpow_pos_of_pos hδ b).le

theorem SizeBound.mono {lam δ b b' s s' r σ : ℝ}
    (h : SizeBound lam δ b s r σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : 0 ≤ s) (hb : b' ≤ b) (hss : s ≤ s') : SizeBound lam δ b' s' r σ := by
  have hpow := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hb
  have hright : s*δ ^ b ≤ s'*δ ^ b' :=
    (mul_le_mul_of_nonneg_left hpow hs).trans
      (mul_le_mul_of_nonneg_right hss (Real.rpow_pos_of_pos hδ b').le)
  exact ⟨h.1.trans hright, h.2.trans hright⟩

/-- Radius-square propagation is separate from the width-sensitive ratio. -/
theorem radius_sq_le (lam r r' : ℝ) (hlam : 0 ≤ lam) (hr' : 0 ≤ r') (hrr : r' ≤ r) :
    lam*r'^2 ≤ lam*r^2 :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr' hrr 2) hlam

theorem SizeBound.of_child_ratio {lam δ b s r σ r' σ' loss c : ℝ}
    (h : SizeBound lam δ b s r σ) (hlam : 0 ≤ lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : 0 ≤ s) (hr' : 0 ≤ r') (hrr : r' ≤ r) (hloss : 0 ≤ loss) (hc : 1 ≤ c)
    (hx : lam*(r'/σ') ≤ (c*s)*δ ^ (b-loss)) :
    SizeBound lam δ (b-loss) (c*s) r' σ' := by
  have hm := h.mono hδ hδ1 hs (by linarith : b-loss ≤ b)
    (le_mul_of_one_le_left hs hc)
  exact ⟨(radius_sq_le lam r r' hlam hr' hrr).trans hm.1, hx⟩

/-- Original SizeBound pays the literal syntactic rowBound, at its exact exponent. -/
theorem scaled_rowBound_le {m : ℕ} {lam δ b s r σ t w : ℝ}
    (h : SizeBound lam δ b s r σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    lam*SourceMeanExecutable.rowBound (m := m) r σ δ t w ≤
      (rowFactor m*s)*δ ^ (b-4*t-w) := by
  have hp : δ ^ b * δ ^ (-4*t-w) = δ ^ (b-4*t-w) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hpow0 : 0 ≤ δ ^ (-4*t-w) := (Real.rpow_pos_of_pos hδ _).le
  have hy := h.1.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : b-4*t-w ≤ b)) hs)
  calc
    lam*SourceMeanExecutable.rowBound (m := m) r σ δ t w =
        256*(m:ℝ)^5*(lam*(r/σ))*δ ^ (-4*t-w)+4*(lam*r^2) := by
      unfold SourceMeanExecutable.rowBound
      simp only [Real.rpow_eq_pow]
      ring
    _ ≤ 256*(m:ℝ)^5*(s*δ ^ b)*δ ^ (-4*t-w)+
        4*(s*δ ^ (b-4*t-w)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h.2 (by positivity)) hpow0)
        (mul_le_mul_of_nonneg_left hy (by norm_num))
    _ = (256*(m:ℝ)^5*s)*(δ ^ b*δ ^ (-4*t-w))+
        4*s*δ ^ (b-4*t-w) := by ring
    _ = _ := by rw [hp]; unfold rowFactor; ring

/-- The source main width coefficient costs exactly two t powers and one w. -/
theorem main_coefficient_le (δ t w R Ds B : ℝ) (n : ℕ)
    (hδ : 0 < δ) (hR : R = δ ^ t)
    (hDsBound : Ds ≤ δ ^ (-t))
    (hn : Real.sqrt n ≤ B*δ ^ (-w)) :
    4*Real.sqrt 5*Ds*Real.sqrt n/R ≤ mainFactor B*δ ^ (-2*t-w) := by
  rw [hR]
  calc
    _ ≤ 4*Real.sqrt 5*δ ^ (-t)*(B*δ ^ (-w))/δ ^ t := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos hδ t).le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hDsBound (by positivity)) hn
        (Real.sqrt_nonneg _) (by positivity)
    _ = mainFactor B*(δ ^ (-t)*δ ^ (-w)*δ ^ (-t)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hδ.le]
      unfold mainFactor
      ring
    _ = _ := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 2
      ring

theorem final_coefficient_le (δ t τ : ℝ) (hδ : 0 < δ)
    (hτ : δ ^ t ≤ τ) :
    2*Real.sqrt 2/τ ≤ 3*δ ^ (-t) := by
  have hp := Real.rpow_pos_of_pos hδ t
  have hτpos := hp.trans_le hτ
  have hnum : 2*Real.sqrt 2 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  calc
    _ ≤ 3/τ := div_le_div_of_nonneg_right hnum hτpos.le
    _ ≤ 3/δ ^ t := div_le_div_of_nonneg_left (by norm_num) hp hτ
    _ = _ := by rw [Real.rpow_neg hδ.le]; rfl

/-- The scalar delta=1 endpoint is defined, but cannot satisfy the actual
mean geometry together with R=delta^t. -/
theorem source_delta_lt_one {m : ℕ} (M : MeanGeometry m) (δ t : ℝ)
    (hδ1 : δ ≤ 1) (hR : M.R = δ ^ t) : δ < 1 := by
  apply lt_of_le_of_ne hδ1
  intro heq
  have hR1 : M.R = 1 := by simpa [heq] using hR
  linarith [M.R_le_half]

end AcceleratedLogConcave.Oracle.RecursiveSize
