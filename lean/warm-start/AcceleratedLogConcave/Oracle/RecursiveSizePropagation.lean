import AcceleratedLogConcave.Oracle.RecursiveSizeBound

/-! One-step sufficient SizeBound propagation through the literal four source
call updates. No reachable-call induction or uniform stability is asserted. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveSize
open Numerics.AffineGraph RecursiveMeanPublicTable RecursiveCallAccounting
variable {m ms n ns : ℕ}

private theorem normalized_product_le {lam u k A K T : ℝ}
    (hu : u ≤ 1) (hk : 0 ≤ k) (hA : 0 ≤ lam*A) (hkK : k ≤ K)
    (hK : 0 ≤ K) (hT : lam*A ≤ T) : lam*(u*k*A) ≤ K*T := by
  calc
    _ = u*(k*(lam*A)) := by ring
    _ ≤ k*(lam*A) := mul_le_of_le_one_left (mul_nonneg hk hA) hu
    _ ≤ K*(lam*A) := mul_le_mul_of_nonneg_right hkK hA
    _ ≤ K*T := mul_le_mul_of_nonneg_left hT hK

/-- Sharp mean-main exponent loss from the actual row bound and source width. -/
theorem mean_main_size (M : MeanGeometry m) (lam δ b s r σ Ds t w B : ℝ)
    (h : SizeBound lam δ b s r σ) (hlam : 0 ≤ lam) (hs : 0 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hDs : 0 ≤ Ds)
    (ht : 0 ≤ t) (hw : 0 ≤ w) (hB : 1 ≤ B)
    (hR : M.R = δ ^ t) (hDsBound : Ds ≤ δ ^ (-t))
    (hn : Real.sqrt n ≤ B*δ ^ (-w)) (i : M.MeanNode) :
    SizeBound lam δ (b-(6*t+2*w)) ((mainFactor B*rowFactor m)*s)
      (M.radius r i)
      (mainWidth n r M.R Ds (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) := by
  have hK : 0 ≤ mainFactor B := (by norm_num : (0:ℝ) ≤ 1).trans (mainFactor_ge_one B hB)
  have hc : 1 ≤ mainFactor B*rowFactor m :=
    (mainFactor_ge_one B hB).trans (le_mul_of_one_le_right hK (rowFactor_ge_one m))
  apply h.of_child_ratio hlam hδ hδ1 hs (M.radius_nonneg r hr i) (M.radius_le r hr i)
    (by positivity) hc
  have hrow := scaled_rowBound_le (m := m) h hδ hδ1 hs ht hw
  have hcoef := main_coefficient_le δ t w M.R Ds B n hδ hR hDsBound hn
  have hk : 0 ≤ 4*Real.sqrt 5*Ds*Real.sqrt n/M.R := div_nonneg (by positivity) M.R_pos.le
  have hA := mul_nonneg hlam (rowBound_nonneg (m := m) r σ δ t w hr hσ hδ)
  have hpow : 0 ≤ δ ^ (-2*t-w) := (Real.rpow_pos_of_pos hδ _).le
  have hp : δ ^ (-2*t-w)*δ ^ (b-4*t-w) =
      δ ^ (b-(6*t+2*w)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [mean_main_ratio_eq]
  calc
    _ ≤ (mainFactor B*δ ^ (-2*t-w))*
        ((rowFactor m*s)*δ ^ (b-4*t-w)) :=
      normalized_product_le (M.normalizedRadius_le_one i) hk hA hcoef (mul_nonneg hK hpow) hrow
    _ = ((mainFactor B*rowFactor m)*s)*
        (δ ^ (-2*t-w)*δ ^ (b-4*t-w)) := by ring
    _ = _ := by rw [hp]

/-- Active-final calls multiply s by three and spend no delta exponent. -/
theorem mean_final_size (M : MeanGeometry m) (lam δ b s r σ : ℝ)
    (h : SizeBound lam δ b s r σ) (hlam : 0 ≤ lam) (hs : 0 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 ≤ r) (hσ : 0 ≤ σ) :
    SizeBound lam δ b (3*s) (r*M.R) (finalWidth M.R σ) := by
  have hm := mean_final_radius_mem M r hr
  have hf : 4/Real.sqrt 3 ≤ (3:ℝ) := by
    have hsqrt : 0 < Real.sqrt 3 := by positivity
    apply (div_le_iff₀ hsqrt).2
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have hx : lam*((r*M.R)/finalWidth M.R σ) ≤ (3*s)*δ ^ (b-0) := by
    rw [mean_final_ratio_eq]
    calc
      _ = (4/Real.sqrt 3)*(lam*(r/σ)) := by ring
      _ ≤ 3*(lam*(r/σ)) := mul_le_mul_of_nonneg_right hf (mul_nonneg hlam (div_nonneg hr hσ))
      _ ≤ 3*(s*δ ^ b) := mul_le_mul_of_nonneg_left h.2 (by norm_num)
      _ = _ := by rw [sub_zero]; ring
  simpa only [sub_zero] using h.of_child_ratio hlam hδ hδ1 hs hm.1 hm.2
    (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (1:ℝ) ≤ 3) hx

theorem sampling_main_size (S : SamplingGeometry ms) (lam δ b s r σ Ds t w B : ℝ)
    (h : SizeBound lam δ b s r σ) (hlam : 0 ≤ lam) (hs : 0 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 ≤ r) (hDs : 0 ≤ Ds)
    (ht : 0 ≤ t) (hw : 0 ≤ w) (hB : 1 ≤ B)
    (hR : S.R = δ ^ t) (hDsBound : Ds ≤ δ ^ (-t))
    (hn : Real.sqrt ns ≤ B*δ ^ (-w)) (i : S.Node) :
    SizeBound lam δ (b-(2*t+w)) (mainFactor B*s) (S.radius r i)
      (mainWidth ns r S.R Ds (r^2)) := by
  have hK : 0 ≤ mainFactor B := (by norm_num : (0:ℝ) ≤ 1).trans (mainFactor_ge_one B hB)
  apply h.of_child_ratio hlam hδ hδ1 hs (S.radius_nonneg r hr i) (S.radius_le r hr i)
    (by positivity) (mainFactor_ge_one B hB)
  have hcoef := main_coefficient_le δ t w S.R Ds B ns hδ hR hDsBound hn
  have hk : 0 ≤ 4*Real.sqrt 5*Ds*Real.sqrt ns/S.R := div_nonneg (by positivity) S.R_pos.le
  have hA : 0 ≤ lam*r^2 := by positivity
  have hpow : 0 ≤ δ ^ (-2*t-w) := (Real.rpow_pos_of_pos hδ _).le
  have hp : δ ^ (-2*t-w)*δ ^ b = δ ^ (b-(2*t+w)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [sampling_main_ratio_eq]
  calc
    _ ≤ (mainFactor B*δ ^ (-2*t-w))*(s*δ ^ b) :=
      normalized_product_le (S.normalizedRadius_le_one i) hk hA hcoef (mul_nonneg hK hpow) h.1
    _ = (mainFactor B*s)*(δ ^ (-2*t-w)*δ ^ b) := by ring
    _ = _ := by rw [hp]

theorem sampling_final_size (S : SamplingGeometry ms) (lam δ b s r σ t : ℝ)
    (h : SizeBound lam δ b s r σ) (hlam : 0 ≤ lam) (hs : 0 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hτ : δ ^ t ≤ S.τ) (i : S.Node) :
    SizeBound lam δ (b-t) (3*s) (S.radius r i) (SourceExecutableTables.samplingFinalWidth S r) := by
  apply h.of_child_ratio hlam hδ hδ1 hs (S.radius_nonneg r hr i) (S.radius_le r hr i) ht
    (by norm_num : (1:ℝ) ≤ 3)
  have hcoef := final_coefficient_le δ t S.τ hδ hτ
  have hτpos : 0 < S.τ := S.R_pos.trans_le S.R_le_τ
  have hk : 0 ≤ 2*Real.sqrt 2/S.τ := by positivity
  have hA : 0 ≤ lam*r^2 := by positivity
  have hpow : 0 ≤ δ ^ (-t) := (Real.rpow_pos_of_pos hδ _).le
  have hp : δ ^ (-t)*δ ^ b = δ ^ (b-t) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [sampling_final_ratio_eq]
  calc
    _ ≤ (3*δ ^ (-t))*(s*δ ^ b) :=
      normalized_product_le (S.normalizedRadius_le_one i) hk hA hcoef (by positivity) h.1
    _ = (3*s)*(δ ^ (-t)*δ ^ b) := by ring
    _ = _ := by rw [hp]

/-- A sufficient one-step source schedule. Quarter-drop families spend at most
10*t and multiply s by the explicit stepFactor; active final spends no exponent.
The desired child SizeBounds are conclusions, never hypotheses. -/
theorem source_children_size (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (lam δ b s r σ Ds t w B : ℝ) (h : SizeBound lam δ b s r σ)
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hr : 0 < r) (hσ : 0 < σ) (hDs : 0 < Ds)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ w) (hwt : w ≤ t) (hB : 1 ≤ B)
    (hR : M.R = δ ^ t) (hSR : S.R = M.R)
    (hDsBound : Ds ≤ δ ^ (-t))
    (hn : Real.sqrt n ≤ B*δ ^ (-w))
    (hns : Real.sqrt ns ≤ B*δ ^ (-w)) :
    (∀ i : Fin n, SizeBound lam δ (b-10*t) (stepFactor m B*s) (M.radius r (nodes i))
      (mainWidth n r M.R Ds (SourceMeanExecutable.rowBound (m := m) r σ δ t w))) ∧
    SizeBound lam δ b (3*s) (r*M.R) (finalWidth M.R σ) ∧
    (∀ i : Fin ns, SizeBound lam δ (b-10*t) (stepFactor m B*s) (S.radius r (snodes i))
      (mainWidth ns r S.R Ds (r^2))) ∧
    (∀ i : Fin ns, SizeBound lam δ (b-10*t) (stepFactor m B*s) (S.radius r (snodes i))
      (SourceExecutableTables.samplingFinalWidth S r)) := by
  have ht : 0 ≤ t := hw.trans hwt
  have hK : 0 ≤ mainFactor B := (by norm_num : (0:ℝ) ≤ 1).trans (mainFactor_ge_one B hB)
  have hD : 0 ≤ rowFactor m := (by norm_num : (0:ℝ) ≤ 1).trans (rowFactor_ge_one m)
  refine ⟨?_, mean_final_size M lam δ b s r σ h hlam hs hδ hδ1 hr.le hσ.le, ?_, ?_⟩
  · intro i
    have hi := mean_main_size M lam δ b s r σ Ds t w B h hlam hs hδ hδ1 hr.le hσ.le
      hDs.le ht hw hB hR hDsBound hn (nodes i)
    exact hi.mono hδ hδ1 (by positivity) (by linarith)
      (mul_le_mul_of_nonneg_right (stepFactor_ge_product m B) hs)
  · intro i
    have hi := sampling_main_size S lam δ b s r σ Ds t w B h hlam hs hδ hδ1 hr.le
      hDs.le ht hw hB (hSR.trans hR) hDsBound hns (snodes i)
    exact hi.mono hδ hδ1 (by positivity) (by linarith)
      (mul_le_mul_of_nonneg_right (stepFactor_ge_main m B hB) hs)
  · intro i
    have hτ : δ ^ t ≤ S.τ := by rw [← hR, ← hSR]; exact S.R_le_τ
    have hi := sampling_final_size S lam δ b s r σ t h hlam hs hδ hδ1 hr.le ht hτ (snodes i)
    exact hi.mono hδ hδ1 (by positivity) (by linarith)
      (mul_le_mul_of_nonneg_right (stepFactor_ge_three m B (by linarith)) hs)

end AcceleratedLogConcave.Oracle.RecursiveSize
