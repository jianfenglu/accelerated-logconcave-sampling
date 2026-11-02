import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Canonical L² lifting with explicit finite-order domination.
These are analytic helper lemmas, not assertions of the warm kernel supplier. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Analysis.DominatedLp
variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [SecondCountableTopology Ω] [BorelSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [TopologicalSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
  [CompleteSpace E] [SecondCountableTopology E] [IsFiniteMeasure μ] in
theorem norm_sq_toLp {g : Ω → E}
    (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ p, ‖g p‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with p hp
  rw [hp, real_inner_self_eq_norm_sq]

omit [SecondCountableTopology Ω] [CompleteSpace E] [SecondCountableTopology E]
  [IsFiniteMeasure μ] in
/-- Joint continuity and one genuine L² envelope give continuity of the canonical L² classes. -/
theorem continuous_toLp_of_dominated
    (g : ℝ → Ω → E)
    (hg : Continuous (Function.uncurry g))
    (B : Ω → ℝ)
    (hB : MemLp B 2 μ)
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 μ) :
    Continuous (fun t => (hm t).toLp (g t)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hc : Continuous (fun t => ∫ p, ‖g t p - g s p‖ ^ 2
      ∂μ) := by
    apply continuous_of_dominated (bound := fun p => (2 * B p)^2)
    · intro t
      exact ((hg.comp (continuous_const.prodMk continuous_id)).sub
        (hg.comp (continuous_const.prodMk continuous_id))).norm.pow 2 |>.aestronglyMeasurable
    · intro t
      filter_upwards [] with p
      have hn : ‖g t p - g s p‖ ≤ 2 * B p :=
        (norm_sub_le _ _).trans (by linarith [hbound t p, hbound s p])
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g t p - g s p‖)]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    · exact (hB.const_mul 2).integrable_sq
    · filter_upwards [] with p
      exact ((hg.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2
  have heq (t : ℝ) :
      dist ((hm t).toLp (g t)) ((hm s).toLp (g s)) =
        Real.sqrt (∫ p, ‖g t p - g s p‖ ^ 2 ∂μ) := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, ← norm_sq_toLp]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp_rw [heq]
  simpa [Function.comp_def] using ((Real.continuous_sqrt.comp hc).continuousAt (x := s)).tendsto

/-- Signed pointwise integration commutes with the canonical L² lift under genuine
joint continuity and a common L² envelope. The proof uses scalar pairings and Fubini. -/
theorem toLp_intervalIntegral_of_dominated
    (g : ℝ → Ω → E)
    (hg : Continuous (Function.uncurry g))
    (B : Ω → ℝ)
    (hB : MemLp B 2 μ)
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 μ)
    (a b : ℝ) :
    ∃ hi : MemLp (fun p => ∫ t in a..b, g t p) 2
        μ,
      hi.toLp (fun p => ∫ t in a..b, g t p) = ∫ t in a..b, (hm t).toLp (g t) := by
  have hmeas : StronglyMeasurable (fun p => ∫ t in a..b, g t p) := by
    unfold intervalIntegral
    exact hg.stronglyMeasurable.integral_prod_left.sub hg.stronglyMeasurable.integral_prod_left
  have hi : MemLp (fun p => ∫ t in a..b, g t p) 2 μ := by
    apply (hB.const_mul |b-a|).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hbound t p)
  refine ⟨hi, ?_⟩
  have hgi (p) : IntervalIntegrable (fun t => g t p) volume a b :=
    (hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hli : IntervalIntegrable (fun t => (hm t).toLp (g t)) volume a b :=
    (continuous_toLp_of_dominated g hg B hB hbound hm).intervalIntegrable a b
  apply ext_inner_left ℝ
  intro w
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    unfold uIoc
    infer_instance
  have hprod : Integrable (fun q : ℝ × Ω =>
      inner ℝ (w q.2) (g q.1 q.2)) ((volume.restrict (uIoc a b)).prod μ) := by
    apply (((Lp.memLp w).norm.integrable_mul hB).comp_snd _).mono'
      ((Lp.aestronglyMeasurable w).comp_snd.inner hg.aestronglyMeasurable)
    filter_upwards [] with q
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hbound q.1 q.2) (norm_nonneg _))
  calc
    inner ℝ w (hi.toLp (fun p => ∫ t in a..b, g t p)) =
        ∫ p, inner ℝ (w p) (∫ t in a..b, g t p) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hi.coeFn_toLp] with p hp
      rw [hp]
    _ = ∫ p, (∫ t in a..b, inner ℝ (w p) (g t p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact ((innerSL ℝ (w p)).intervalIntegral_comp_comm (hgi p)).symm
    _ = ∫ t in a..b, ∫ p, inner ℝ (w p) (g t p) ∂μ :=
      (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in a..b, inner ℝ w ((hm t).toLp (g t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hm t).coeFn_toLp] with p hp
      rw [hp]
    _ = inner ℝ w (∫ t in a..b, (hm t).toLp (g t)) :=
      (innerSL ℝ w).intervalIntegral_comp_comm hli


/-- Lift an actual pointwise derivative on an open interval. Only the derivative
field needs a common L² envelope. No derivative of that field is requested. -/
theorem hasDerivAt_toLp_of_dominated
    (f g : ℝ → Ω → E)
    (hg : Continuous (Function.uncurry g))
    (B : Ω → ℝ) (hB : MemLp B 2 μ)
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hmf : ∀ t, MemLp (f t) 2 μ) (hmg : ∀ t, MemLp (g t) 2 μ)
    {a b : ℝ}
    (hd : ∀ t ∈ Ioo a b, ∀ p, HasDerivAt (fun q => f q p) (g t p) t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun q => (hmf q).toLp (f q)) ((hmg t).toLp (g t)) t := by
  let F (q : ℝ) := (hmf q).toLp (f q)
  let G (q : ℝ) := (hmg q).toLp (g q)
  have hG : Continuous G := continuous_toLp_of_dominated g hg B hB hbound hmg
  have heq (u : ℝ) (hu : u ∈ Ioo a b) : F u = F t + ∫ q in t..u, G q := by
    obtain ⟨hi, hli⟩ := toLp_intervalIntegral_of_dominated g hg B hB hbound hmg t u
    have hraw (p : Ω) : (∫ q in t..u, g q p) = f u p - f t p := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro q hq
        exact hd q (ordConnected_Ioo.uIcc_subset ht hu hq) p
      · exact (hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable t u
    have he : hi.toLp (fun p => ∫ q in t..u, g q p) = F u - F t := by
      apply Lp.ext
      filter_upwards [hi.coeFn_toLp, Lp.coeFn_sub (F u) (F t),
        (hmf u).coeFn_toLp, (hmf t).coeFn_toLp] with p h1 h2 h3 h4
      rw [h1, h2, Pi.sub_apply, h3, h4]
      exact hraw p
    rw [hli] at he
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  have hp : HasDerivAt (fun u => ∫ q in t..u, G q) (G t) t :=
    intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable t t)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
  have hp' : HasDerivAt (fun u => F t + ∫ q in t..u, G q) (G t) t := by
    convert! hp.const_add (F t) using 1
  apply hp'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact heq u hu

/-- A finite derivative ladder lifts to C^n in L². The final field needs
continuity and domination, with no derivative assumption at order n. No regularity or integrability premise is made at any order above n. -/
theorem contDiffOn_toLp_of_finite_ladder
    (n : ℕ) (f : ℕ → ℝ → Ω → E)
    (hm : ∀ k, k ≤ n → ∀ t, MemLp (f k t) 2 μ)
    (hc : ∀ k ≤ n, Continuous (Function.uncurry (f k)))
    (B : ℕ → Ω → ℝ) (hB : ∀ k ≤ n, MemLp (B k) 2 μ)
    (hbound : ∀ k ≤ n, ∀ t p, ‖f k t p‖ ≤ B k p)
    {a b : ℝ}
    (hd : ∀ k < n, ∀ t ∈ Ioo a b, ∀ p,
      HasDerivAt (fun q => f k q p) (f (k + 1) t p) t) :
    ContDiffOn ℝ n (fun t => (hm 0 (Nat.zero_le n) t).toLp (f 0 t)) (Ioo a b) := by
  induction n generalizing f B with
  | zero =>
      exact contDiffOn_zero.mpr (continuous_toLp_of_dominated (f 0) (hc 0 le_rfl) (B 0)
        (hB 0 le_rfl) (hbound 0 le_rfl) (hm 0 le_rfl)).continuousOn
  | succ n ih =>
      have hstep (t : ℝ) (ht : t ∈ Ioo a b) :
          HasDerivAt (fun q => (hm 0 (Nat.zero_le (n + 1)) q).toLp (f 0 q))
            ((hm 1 (by omega) t).toLp (f 1 t)) t := by
        exact hasDerivAt_toLp_of_dominated (f 0) (f 1) (hc 1 (by omega))
          (B 1) (hB 1 (by omega)) (hbound 1 (by omega)) (hm 0 (by omega)) (hm 1 (by omega))
          (hd 0 (by omega)) ht
      have htail : ContDiffOn ℝ n (fun t => (hm 1 (by omega) t).toLp (f 1 t)) (Ioo a b) := by
        exact ih (fun k => f (k + 1)) (fun k hk => hm (k + 1) (by omega))
          (fun k hk => hc (k + 1) (by omega)) (fun k => B (k + 1))
          (fun k hk => hB (k + 1) (by omega))
          (fun k hk => hbound (k + 1) (by omega))
          (fun k hk => hd (k + 1) (by omega))
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨fun t ht => (hstep t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · simp
      · exact htail.congr (fun t ht => (hstep t ht).deriv)

/-- Local-in-time version. Domination and joint continuity are required only on
the compact slab. Projection is used solely to invoke the integral-lifting
lemma; every derivative in the conclusion is strictly inside the slab. -/
theorem contDiffOn_toLp_of_finite_ladder_on_Icc
    (n : ℕ) (f : ℕ → ℝ → Ω → E)
    (hm : ∀ k, k ≤ n → ∀ t, MemLp (f k t) 2 μ)
    {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ k ≤ n, ContinuousOn (Function.uncurry (f k))
      (Icc a b ×ˢ (univ : Set Ω)))
    (B : ℕ → Ω → ℝ) (hB : ∀ k ≤ n, MemLp (B k) 2 μ)
    (hbound : ∀ k ≤ n, ∀ t ∈ Icc a b, ∀ p, ‖f k t p‖ ≤ B k p)
    (hd : ∀ k < n, ∀ t ∈ Ioo a b, ∀ p,
      HasDerivAt (fun q => f k q p) (f (k + 1) t p) t) :
    ContDiffOn ℝ n (fun t => (hm 0 (Nat.zero_le n) t).toLp (f 0 t)) (Ioo a b) := by
  let c (t : ℝ) : ℝ := projIcc a b hab t
  let g (k : ℕ) (t : ℝ) (p : Ω) := f k (c t) p
  have hccont : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcmem (t : ℝ) : c t ∈ Icc a b := (projIcc a b hab t).property
  have hceq {t : ℝ} (ht : t ∈ Icc a b) : c t = t := congrArg Subtype.val (projIcc_of_mem hab ht)
  have hgm (k : ℕ) (hk : k ≤ n) (t : ℝ) : MemLp (g k t) 2 μ := hm k hk (c t)
  have hgc (k : ℕ) (hk : k ≤ n) : Continuous (Function.uncurry (g k)) := by
    exact (hc k hk).comp_continuous
      ((hccont.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨hcmem p.1, mem_univ p.2⟩)
  have hgb (k : ℕ) (hk : k ≤ n) (t : ℝ) (p : Ω) : ‖g k t p‖ ≤ B k p :=
    hbound k hk (c t) (hcmem t) p
  have hgd (k : ℕ) (hk : k < n) (t : ℝ) (ht : t ∈ Ioo a b) (p : Ω) :
      HasDerivAt (fun q => g k q p) (g (k + 1) t p) t := by
    have he : (fun q => g k q p) =ᶠ[𝓝 t] (fun q => f k q p) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with q hq
      exact congrArg (fun u => f k u p) (hceq ⟨hq.1.le, hq.2.le⟩)
    have h := (hd k hk t ht p).congr_of_eventuallyEq he
    simpa only [g, hceq ⟨ht.1.le, ht.2.le⟩] using h
  have H := contDiffOn_toLp_of_finite_ladder n g hgm hgc B hB hgb hgd
  apply H.congr
  intro t ht
  apply MemLp.toLp_congr
  filter_upwards [] with p
  exact congrArg (fun u => f 0 u p) (hceq ⟨ht.1.le, ht.2.le⟩).symm

end AcceleratedLogConcave.Analysis.DominatedLp
