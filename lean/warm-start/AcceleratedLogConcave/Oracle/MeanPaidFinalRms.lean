import AcceleratedLogConcave.Numerics.SharedLayerRms

/-! Paid-final difference-only L2 propagation. The final benchmark child errors
remain explicit premises. Exact original P and designated final inputs cancel
pathwise, before L2 is used. This is not a reference-law or D2 construction. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.MeanPaidFinalRms
open MeasureTheory Numerics
open scoped BigOperators NNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- No absolute integrability of f_j is needed beyond the stated differences. -/
theorem weighted_norm_le (μ : Measure Ω) (w : Fin m → ℝ) (f : Fin m → Ω → E)
    (hf : ∀ i, MemLp (f i) 2 μ) (B : Fin m → ℝ)
    (hB : ∀ i, ‖(hf i).toLp (f i)‖ ≤ B i) :
    ∃ hs : MemLp (fun ω => ∑ i, w i • f i ω) 2 μ,
      ‖hs.toLp (fun ω => ∑ i, w i • f i ω)‖ ≤ ∑ i, |w i| * B i := by
  have hs : MemLp (fun ω => ∑ i, w i • f i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => (hf i).const_smul (w i))
  have hid : hs.toLp (fun ω => ∑ i, w i • f i ω) =
      ∑ i, w i • (hf i).toLp (f i) := by
    apply Lp.ext
    filter_upwards [hs.coeFn_toLp,
      AffineResidual.coeFn_weighted_sum w (fun i => (hf i).toLp (f i)),
      ae_all_iff.2 (fun i => (hf i).coeFn_toLp)] with ω hsω hw hfω
    rw [hsω,hw]
    simp only [hfω]
  refine ⟨hs,?_⟩
  rw [hid]
  calc
    _ ≤ ∑ i, ‖w i • (hf i).toLp (f i)‖ := norm_sum_le _ _
    _ = ∑ i, |w i| * ‖(hf i).toLp (f i)‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)

/-- This algebra is the retained correction, with exactly the same P and P_i. -/
theorem paid_difference (σ : ℝ) (w width : Fin m → ℝ)
    (P : E) (Pi U X Y : Fin m → E) (F : Fin m → E → E) :
    (σ • P + ∑ i, w i • (F i (X i) - width i • Pi i)) -
      (σ • P + ∑ i, w i • U i) =
      (∑ i, w i • (F i (X i) - F i (Y i))) +
        ∑ i, w i • (F i (Y i) - width i • Pi i - U i) := by
  simp only [smul_sub,Finset.sum_sub_distrib]
  abel

/-- Finite final propagation from an explicit node-error bound D. The norm is
max_i ||error_i||_L2, never ||max_i error_i||_L2. -/
theorem paid_error_bound (μ : Measure Ω) (σ : ℝ) (w width : Fin m → ℝ)
    (P : Ω → E) (Pi U : Fin m → Ω → E)
    (X Y : Fin n → Ω → E) (active : Fin m → Fin n)
    (F : Fin m → Ω → E → E) (κ : ℝ≥0) (D : ℝ) (ε : Fin m → ℝ)
    (hLip : ∀ i ω, LipschitzWith κ (F i ω))
    (herr : ∀ j, MemLp (fun ω => X j ω - Y j ω) 2 μ)
    (hD : ∀ j, ‖(herr j).toLp (fun ω => X j ω - Y j ω)‖ ≤ D)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun ω => F i ω (X (active i) ω) - F i ω (Y (active i) ω)) μ)
    (hchild : ∀ i, MemLp (fun ω => F i ω (Y (active i) ω) - width i • Pi i ω - U i ω) 2 μ)
    (hchildBound : ∀ i, ‖(hchild i).toLp
      (fun ω => F i ω (Y (active i) ω) - width i • Pi i ω - U i ω)‖ ≤ ε i) :
    let err := fun ω => (σ • P ω + ∑ i, w i • (F i ω (X (active i) ω) - width i • Pi i ω)) -
      (σ • P ω + ∑ i, w i • U i ω)
    ∃ hout : MemLp err 2 μ,
      ‖hout.toLp err‖ ≤ (∑ i, |w i|) * ((κ : ℝ)*D) + ∑ i, |w i| *ε i := by
  dsimp only
  let Δ := fun i ω => F i ω (X (active i) ω) - F i ω (Y (active i) ω)
  let H := fun i ω => F i ω (Y (active i) ω) - width i • Pi i ω - U i ω
  have hd (i : Fin m) : MemLp (Δ i) 2 μ :=
    SharedLayerRms.memLp_fixedTape_sub (F i) (X (active i)) (Y (active i)) κ
      (hLip i) (hmeas i) (herr (active i))
  have hdB (i : Fin m) : ‖(hd i).toLp (Δ i)‖ ≤ (κ : ℝ)*D :=
    (SharedLayerRms.norm_toLp_fixedTape_sub_le (F i) (X (active i)) (Y (active i)) κ
      (hLip i) (herr (active i)) (hd i)).trans
        (mul_le_mul_of_nonneg_left (hD (active i)) κ.coe_nonneg)
  obtain ⟨hΔ,hΔB⟩ := weighted_norm_le μ w Δ hd (fun _ => (κ : ℝ)*D) hdB
  obtain ⟨hH,hHB⟩ := weighted_norm_le μ w H hchild ε hchildBound
  let f := fun ω => (σ • P ω + ∑ i, w i • (F i ω (X (active i) ω) - width i • Pi i ω)) -
    (σ • P ω + ∑ i, w i • U i ω)
  have he (ω : Ω) : f ω = (∑ i, w i • Δ i ω) + ∑ i, w i • H i ω :=
    paid_difference σ w width (P ω) (fun i => Pi i ω) (fun i => U i ω)
      (fun i => X (active i) ω) (fun i => Y (active i) ω) (fun i => F i ω)
  have hout : MemLp f 2 μ := (hΔ.add hH).ae_eq (Filter.Eventually.of_forall fun ω => (he ω).symm)
  have hid : hout.toLp f = hΔ.toLp (fun ω => ∑ i, w i • Δ i ω) +
      hH.toLp (fun ω => ∑ i, w i • H i ω) := by
    apply Lp.ext
    filter_upwards [hout.coeFn_toLp,hΔ.coeFn_toLp,hH.coeFn_toLp,
      Lp.coeFn_add (hΔ.toLp _) (hH.toLp _)] with ω ho hd hh ha
    rw [ho,ha]
    simp only [_root_.Pi.add_apply, hd, hh]
    exact he ω
  refine ⟨hout,?_⟩
  rw [hid]
  calc
    _ ≤ ‖hΔ.toLp (fun ω => ∑ i, w i • Δ i ω)‖ +
        ‖hH.toLp (fun ω => ∑ i, w i • H i ω)‖ := norm_add_le _ _
    _ ≤ (∑ i, |w i| *((κ : ℝ)*D)) + ∑ i, |w i| *ε i := add_le_add hΔB hHB
    _ = _ := by rw [Finset.sum_mul]

end AcceleratedLogConcave.Oracle.MeanPaidFinalRms
