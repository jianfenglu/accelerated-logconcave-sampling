import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!

-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AcceleratedLogConcave.Analysis.FixedCut
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Non-strict variable-coefficient comparison by strict epsilon barriers.
K bounds only the known scalar coefficient a, never the unknown solution. -/
theorem forward_comparison {X X' : ℝ → V} {a f B : ℝ → ℝ} {b K : ℝ}
    (hX : ContinuousOn X (Icc 0 b))
    (hX' : ∀ s ∈ Ico 0 b, HasDerivWithinAt X (X' s) (Ici s) s)
    (hB : ContinuousOn B (Icc 0 b))
    (hB' : ∀ s ∈ Ico 0 b, HasDerivWithinAt B (a s * B s + f s) (Ici s) s)
    (h0 : ‖X 0‖ ≤ B 0)
    (ha : ∀ s ∈ Ico 0 b, a s ≤ K)
    (hbound : ∀ s ∈ Ico 0 b, ‖X' s‖ ≤ a s * ‖X s‖ + f s)
    {t : ℝ} (ht : t ∈ Icc 0 b) : ‖X t‖ ≤ B t := by
  have heps : ∀ ε ∈ Ioi (0:ℝ), ‖X t‖ ≤ B t + ε * Real.exp ((K+1)*t) := by
    intro ε hε
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hX hX'
      (B := fun s => B s + ε * Real.exp ((K+1)*s))
      (B' := fun s => a s * B s + f s + ε * (Real.exp ((K+1)*s) * (K+1)))
    · simpa using h0.trans (le_add_of_nonneg_right hε.le)
    · exact hB.add (by fun_prop)
    · intro s hs
      have hd := (((hasDerivAt_id s).const_mul (K+1)).exp.const_mul ε)
      convert (hB' s hs).add hd.hasDerivWithinAt using 1
      · rfl
      · simp
    · intro s hs heq
      have hp : 0 < ε * Real.exp ((K+1)*s) := mul_pos hε (Real.exp_pos _)
      have hk := ha s hs
      have hh := hbound s hs
      rw [heq] at hh
      nlinarith
    · exact ht
  have hc : ContinuousWithinAt (fun ε : ℝ => B t + ε * Real.exp ((K+1)*t))
      (Ioi 0) 0 := by fun_prop
  have h := continuousWithinAt_const.closure_le (by simp : (0:ℝ) ∈ closure (Ioi 0)) hc heps
  simpa using h

/-- Backward version on a closed slab, including the singleton slab b=0.
No derivative uniqueness at endpoints and no division by b is used. -/
theorem backward_comparison {X X' : ℝ → V} {a f B : ℝ → ℝ} {b K : ℝ}
    (hX : ContinuousOn X (Icc 0 b))
    (hX' : ∀ s ∈ Icc 0 b, HasDerivWithinAt X (X' s) (Icc 0 b) s)
    (hB : ContinuousOn B (Icc 0 b))
    (hB' : ∀ s ∈ Icc 0 b, HasDerivWithinAt B (-(a s * B s + f s)) (Icc 0 b) s)
    (hb : ‖X b‖ ≤ B b)
    (ha : ∀ s ∈ Icc 0 b, a s ≤ K)
    (hbound : ∀ s ∈ Icc 0 b, ‖X' s‖ ≤ a s * ‖X s‖ + f s)
    {t : ℝ} (ht : t ∈ Icc 0 b) : ‖X t‖ ≤ B t := by
  have hm (s : ℝ) (hs : s ∈ Icc 0 b) : b-s ∈ Icc 0 b := by
    constructor <;> linarith [hs.1, hs.2]
  have hr (s : ℝ) : HasDerivAt (fun u : ℝ => b-u) (-1) s := by
    convert (hasDerivAt_const s b).sub (hasDerivAt_id s) using 1
    · rfl
    · simp
  have hZ (s : ℝ) (hs : s ∈ Ico 0 b) :
      HasDerivWithinAt (fun u => X (b-u)) (-X' (b-s)) (Ici s) s := by
    have hd := (hX' (b-s) (hm s ⟨hs.1,hs.2.le⟩)).hasFDerivWithinAt.comp_hasDerivWithinAt
      s (hr s).hasDerivWithinAt hm
    have hd' : HasDerivWithinAt (fun u => X (b-u)) (-X' (b-s)) (Icc 0 b) s := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul, Function.comp_def] using hd
    apply hd'.mono_of_mem_nhdsWithin
    exact inter_mem
      (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hs.1))
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hs.2))
  have hR (s : ℝ) (hs : s ∈ Ico 0 b) :
      HasDerivWithinAt (fun u => B (b-u))
        (a (b-s) * B (b-s) + f (b-s)) (Ici s) s := by
    have hd := (hB' (b-s) (hm s ⟨hs.1,hs.2.le⟩)).hasFDerivWithinAt.comp_hasDerivWithinAt
      s (hr s).hasDerivWithinAt hm
    have hd' : HasDerivWithinAt (fun u => B (b-u))
        (a (b-s) * B (b-s) + f (b-s)) (Icc 0 b) s := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul, neg_neg, Function.comp_def] using hd
    apply hd'.mono_of_mem_nhdsWithin
    exact inter_mem
      (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hs.1))
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hs.2))
  have h := forward_comparison
    (hX.comp (continuous_const.sub continuous_id).continuousOn hm) hZ
    (hB.comp (continuous_const.sub continuous_id).continuousOn hm) hR
    (by simpa using hb)
    (fun s hs => ha (b-s) (hm s ⟨hs.1,hs.2.le⟩))
    (fun s hs => by simpa only [norm_neg, Function.comp_def, Pi.sub_apply, id_eq] using hbound (b-s) (hm s ⟨hs.1,hs.2.le⟩))
    (hm t ht)
  have htback : b-(b-t) = t := by ring
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, htback] using h

/-- Exact integrating-factor form; equal to the usual exponential-weighted
Volterra integral. No positivity or division by alpha is required. -/
def envelope (α b δ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-α*t^2/2) *
    (Real.exp (α*b^2/2)*δ + ∫ s in t..b, Real.exp (α*s^2/2)*f s)

 theorem envelope_terminal (α b δ : ℝ) (f : ℝ → ℝ) : envelope α b δ f b = δ := by
  simp only [envelope, intervalIntegral.integral_same, add_zero]
  rw [← mul_assoc, ← Real.exp_add]
  have h : -α*b^2/2 + α*b^2/2 = 0 := by ring
  rw [h, Real.exp_zero, one_mul]

 theorem envelope_derivative (α b δ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (envelope α b δ f) (-(α*t*envelope α b δ f t + f t)) t := by
  have hg : Continuous (fun s : ℝ => Real.exp (α*s^2/2)*f s) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable t b)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hp : HasDerivAt (fun s : ℝ => -α*s^2/2) (-α*t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (-α)).div_const 2 using 1
    · rfl
    · dsimp; ring
  have hd := hp.exp.mul (hi.const_add (Real.exp (α*b^2/2)*δ))
  convert hd using 1
  · rfl
  dsimp [envelope]
  have he : Real.exp (-α*t^2/2) * Real.exp (α*t^2/2) = 1 := by
    rw [← Real.exp_add]
    have h : -α*t^2/2 + α*t^2/2 = 0 := by ring
    rw [h, Real.exp_zero]
  nlinarith [congrArg (fun z : ℝ => z * f t) he]

/-- Exact forcing and exact terminal size, with a(s)=alpha*s. Its hypotheses
are regularity plus a local derivative estimate, not an unknown norm budget. -/
theorem backward_linear_time_bound {X X' : ℝ → V} {f : ℝ → ℝ} {α b δ : ℝ}
    (hα : 0 ≤ α) (hf : Continuous f)
    (hX : ContinuousOn X (Icc 0 b))
    (hX' : ∀ s ∈ Icc 0 b, HasDerivWithinAt X (X' s) (Icc 0 b) s)
    (hb : ‖X b‖ ≤ δ)
    (hbound : ∀ s ∈ Icc 0 b, ‖X' s‖ ≤ α*s*‖X s‖ + f s)
    {t : ℝ} (ht : t ∈ Icc 0 b) : ‖X t‖ ≤ envelope α b δ f t := by
  apply backward_comparison hX hX'
    (fun s _ => (envelope_derivative α b δ hf s).continuousAt.continuousWithinAt)
    (fun s _ => (envelope_derivative α b δ hf s).hasDerivWithinAt)
    (by simpa only [envelope_terminal] using hb)
    (K := α*b) (fun s hs => mul_le_mul_of_nonneg_left hs.2 hα) hbound ht

/-- Homogeneous terminal estimate with the sharp quadratic clock. -/
theorem backward_homogeneous_bound {X X' : ℝ → V} {α b δ : ℝ}
    (hα : 0 ≤ α)
    (hX : ContinuousOn X (Icc 0 b))
    (hX' : ∀ s ∈ Icc 0 b, HasDerivWithinAt X (X' s) (Icc 0 b) s)
    (hb : ‖X b‖ ≤ δ)
    (hbound : ∀ s ∈ Icc 0 b, ‖X' s‖ ≤ α*s*‖X s‖)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ‖X t‖ ≤ δ * Real.exp (α*(b^2-t^2)/2) := by
  have h := backward_linear_time_bound hα (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
    hX hX' hb (fun s hs => by simpa using hbound s hs) ht
  have he : envelope α b δ (fun _ => 0) t = δ * Real.exp (α*(b^2-t^2)/2) := by
    simp only [envelope, mul_zero, intervalIntegral.integral_zero, add_zero]
    rw [← mul_assoc, ← Real.exp_add]
    rw [mul_comm]
    congr 2; ring
  rwa [he] at h

/-- The scalar induction step when the proper-partition forcing is bounded
by alpha*s times a time-independent nonnegative order constant C. This keeps
alpha=0, b=0 and C=0 and uses no division by any of them. -/
theorem backward_proportional_forcing {X X' : ℝ → V} {α b C : ℝ}
    (hα : 0 ≤ α)
    (hX : ContinuousOn X (Icc 0 b))
    (hX' : ∀ s ∈ Icc 0 b, HasDerivWithinAt X (X' s) (Icc 0 b) s)
    (hb : X b = 0)
    (hbound : ∀ s ∈ Icc 0 b, ‖X' s‖ ≤ α*s*‖X s‖ + α*s*C)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ‖X t‖ ≤ C * (Real.exp (α*(b^2-t^2)/2)-1) := by
  let B : ℝ → ℝ := fun s => C * (Real.exp (α*(b^2-s^2)/2)-1)
  have hd (s : ℝ) : HasDerivAt B (-(α*s*B s + α*s*C)) s := by
    have hp : HasDerivAt (fun u : ℝ => α*(b^2-u^2)/2) (-α*s) s := by
      convert ((((hasDerivAt_const s (b^2)).sub ((hasDerivAt_id s).pow 2)).const_mul α).div_const 2) using 1
      · rfl
      · dsimp; ring
    convert (hp.exp.sub_const 1).const_mul C using 1
    dsimp [B]; ring
  apply backward_comparison hX hX'
    (fun s _ => (hd s).continuousAt.continuousWithinAt)
    (fun s _ => (hd s).hasDerivWithinAt)
    (by simp [B, hb])
    (K := α*b) (fun s hs => mul_le_mul_of_nonneg_left hs.2 hα) hbound ht

end AcceleratedLogConcave.Analysis.FixedCut
