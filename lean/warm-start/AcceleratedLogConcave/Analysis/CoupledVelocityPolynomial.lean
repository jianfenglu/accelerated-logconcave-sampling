import AcceleratedLogConcave.Analysis.PolynomialEnvelope
import AcceleratedLogConcave.Analysis.ODEJetPolynomial
import AcceleratedLogConcave.Analysis.PositiveVarianceSlab
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Polynomial mixed jets of the actual coupled-state velocity. The derivative
set is the fixed open time domain (-1,1), with every spatial/operator
coordinate unrestricted. Bounds hold on the closed time slab only.

The order-n theorem takes quantitative M/U1 hypotheses only through n.
All-order smoothness is qualitative. No new flow, global Lipschitz bound,
compactness of the whole slab, or order-(n+1) bound is used.

The closure uses the finite polynomial envelope and actual-state-jet
recurrence suppliers.
-/
noncomputable section
open Set Function
open scoped ContDiff

namespace AcceleratedLogConcave.Analysis.CoupledVelocityPolynomial

section Closure
variable {P X Y G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The domain of differentiation U and the set of uniform bounds S are
kept separate. The polynomial weight includes every input coordinate. -/
def PolynomialJetBound (U S : Set P) (f : P → G) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ p ∈ S,
    ‖iteratedFDerivWithin ℝ n f U p‖ ≤ C * (1 + ‖p‖) ^ N

theorem polynomialJetBound_const (U S : Set P) (c : G) (n : ℕ) :
    PolynomialJetBound U S (fun _ => c) n := by
  refine ⟨‖c‖, norm_nonneg _, 0, ?_⟩
  intro p hp
  cases n with
  | zero => simp only [norm_iteratedFDerivWithin_zero, pow_zero, mul_one, le_refl]
  | succ n =>
    rw [iteratedFDerivWithin_succ_const, Pi.zero_apply, norm_zero, pow_zero, mul_one]
    exact norm_nonneg c

theorem polynomialJetBound_linear {U S : Set P}
    (hU : UniqueDiffOn ℝ U) (hSU : S ⊆ U) (L : P →L[ℝ] G) (n : ℕ) :
    PolynomialJetBound U S L n := by
  refine ⟨‖L‖, norm_nonneg _, 1, ?_⟩
  intro p hp
  simpa only [pow_one] using
    ODEJet.norm_iteratedFDerivWithin_linear_le hU (hSU hp) L n

/-- A fixed norm-at-most-one linear pullback consumes exactly the same jet
order, and does not enlarge the radial polynomial weight. -/
theorem polynomialJetBound_pullback
    {U S : Set X} (hU : IsOpen U) (hSU : S ⊆ U)
    {f : X → G} (hf : ContDiffOn ℝ ∞ f U)
    (L : P →L[ℝ] X) (hL : ‖L‖ ≤ 1) (n : ℕ)
    (hb : PolynomialJetBound U S f n) :
    PolynomialJetBound (L ⁻¹' U) (L ⁻¹' S) (f ∘ L) n := by
  obtain ⟨C, hC, N, hb⟩ := hb
  refine ⟨C, hC, N, ?_⟩
  intro p hp
  have hLn : ‖L‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  have hLp : ‖L p‖ ≤ ‖p‖ :=
    (L.le_opNorm p).trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hL (norm_nonneg p))
  rw [L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    (hU.preimage L.continuous).uniqueDiffOn (hSU hp)
    (by simp : (n : ℕ∞ω) ≤ ∞)]
  calc
    _ ≤ ‖iteratedFDerivWithin ℝ n f U (L p)‖ * ‖L‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDerivWithin ℝ n f U (L p)).norm_compContinuousLinearMap_le
          (fun _ : Fin n => L)
    _ ≤ ‖iteratedFDerivWithin ℝ n f U (L p)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hLn
    _ ≤ C * (1 + ‖L p‖) ^ N := hb (L p) hp
    _ ≤ C * (1 + ‖p‖) ^ N := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hLp) N) hC

/-- Polynomial closure under a fixed bilinear map of norm at most one.
The finite envelope includes precisely the orders 0,...,n of both factors. -/
theorem polynomialJetBound_bilinear
    {U S : Set P} (hU : UniqueDiffOn ℝ U) (hSU : S ⊆ U)
    (B : X →L[ℝ] Y →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    {f : P → X} {g : P → Y}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ)
    (hfbound : ∀ i ≤ n, PolynomialJetBound U S f i)
    (hgbound : ∀ i ≤ n, PolynomialJetBound U S g i) :
    PolynomialJetBound U S (fun p => B (f p) (g p)) n := by
  let R (p : P) : ℝ := 1 + ‖p‖
  have hR : ∀ p ∈ S, 1 ≤ R p :=
    fun p _ => le_add_of_nonneg_right (norm_nonneg p)
  let a : (Fin (n + 1) ⊕ Fin (n + 1)) → P → ℝ :=
    Sum.elim (fun i p => ‖iteratedFDerivWithin ℝ i.val f U p‖)
      (fun i p => ‖iteratedFDerivWithin ℝ i.val g U p‖)
  have ha : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p ∈ S, a i p ≤ C * R p ^ N := by
    intro i
    rcases i with i | i
    · exact hfbound i.val (Nat.lt_succ_iff.mp i.isLt)
    · exact hgbound i.val (Nat.lt_succ_iff.mp i.isLt)
  obtain ⟨A, hA, N, hbound⟩ :=
    PolynomialEnvelope.exists_common_finite_polynomial_bound hR ha
  let H : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H * A ^ 2, mul_nonneg hH (sq_nonneg A), N * 2, ?_⟩
  intro p hp
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U p‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g U p‖ :=
      B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hf hg hU
        (hSU hp) (by simp) hB
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (A * R p ^ N) * (A * R p ^ N) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      have hj : n - i < n + 1 := Nat.lt_succ_of_le (Nat.sub_le n i)
      have hfi := hbound (Sum.inl ⟨i, hi'⟩) p hp
      have hgi := hbound (Sum.inr ⟨n - i, hj⟩) p hp
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfi (by positivity)) hgi
        (norm_nonneg _) (mul_nonneg (by positivity)
          (mul_nonneg (zero_le_one.trans hA)
            (pow_nonneg (zero_le_one.trans (hR p hp)) _)))
    _ = (H * A ^ 2) * (1 + ‖p‖) ^ (N * 2) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      change H * (A * R p ^ N) * (A * R p ^ N) = _
      rw [mul_assoc, ← pow_two, mul_pow, ← pow_mul, ← mul_assoc]

theorem polynomialJetBound_smul
    {U S : Set P} (hU : UniqueDiffOn ℝ U) (hSU : S ⊆ U)
    {f : P → ℝ} {g : P → G}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ)
    (hfbound : ∀ i ≤ n, PolynomialJetBound U S f i)
    (hgbound : ∀ i ≤ n, PolynomialJetBound U S g i) :
    PolynomialJetBound U S (fun p => f p • g p) n :=
  polynomialJetBound_bilinear hU hSU
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] G →L[ℝ] G)
    ContinuousLinearMap.opNorm_lsmul_le hf hg n hfbound hgbound

/-- Pairing at a fixed order needs only the two bounds at that order. -/
theorem polynomialJetBound_prod
    {U S : Set P} (hU : UniqueDiffOn ℝ U) (hSU : S ⊆ U)
    {f : P → X} {g : P → Y}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ) (hfb : PolynomialJetBound U S f n)
    (hgb : PolynomialJetBound U S g n) :
    PolynomialJetBound U S (fun p => (f p, g p)) n := by
  obtain ⟨C, hC, N, hfb⟩ := hfb
  obtain ⟨D, hD, M, hgb⟩ := hgb
  refine ⟨C + D, add_nonneg hC hD, N + M, ?_⟩
  intro p hp
  have hR : 1 ≤ 1 + ‖p‖ := le_add_of_nonneg_right (norm_nonneg p)
  have hf' : ‖iteratedFDerivWithin ℝ n f U p‖ ≤
      (C + D) * (1 + ‖p‖) ^ (N + M) :=
    (hfb p hp).trans (mul_le_mul (le_add_of_nonneg_right hD)
      (pow_le_pow_right₀ hR (Nat.le_add_right N M))
      (by positivity) (add_nonneg hC hD))
  have hg' : ‖iteratedFDerivWithin ℝ n g U p‖ ≤
      (C + D) * (1 + ‖p‖) ^ (N + M) :=
    (hgb p hp).trans (mul_le_mul (le_add_of_nonneg_left hC)
      (pow_le_pow_right₀ hR (Nat.le_add_left M N))
      (by positivity) (add_nonneg hC hD))
  rw [iteratedFDerivWithin_prodMk (hf p (hSU hp)) (hg p (hSU hp))
    hU (hSU hp) (by simp : (n : ℕ∞ω) ≤ ∞),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le hf' hg'
end Closure

section Coupled
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev CoupledState := E × (E →L[ℝ] E)
abbrev CoupledSpaceTime := ℝ × CoupledState E

def openDomain : Set (ℝ × E) := Prod.fst ⁻¹' Ioo (-1 : ℝ) 1

def closedSlab (b : ℝ) : Set (ℝ × E) :=
  Prod.fst ⁻¹' Icc (PositiveVarianceSlab.left b) (PositiveVarianceSlab.right b)

omit [NormedSpace ℝ E] in
theorem isOpen_openDomain : IsOpen (openDomain E) :=
  isOpen_Ioo.preimage continuous_fst

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem closedSlab_subset_openDomain {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    closedSlab E b ⊆ openDomain E :=
  fun _ hp => PositiveVarianceSlab.construction_subset hb0 hb1 hp

/-- Fixed projection removing the operator coordinate, not a flow-dependent map. -/
def timeSpaceProjection : CoupledSpaceTime E →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.fst ℝ ℝ (CoupledState E)).prod
    ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).comp
      (ContinuousLinearMap.snd ℝ ℝ (CoupledState E)))

def matrixProjection : CoupledSpaceTime E →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
    (ContinuousLinearMap.snd ℝ ℝ (CoupledState E))

def timeCoefficient (r : ℝ) : CoupledSpaceTime E →L[ℝ] ℝ :=
  r • ContinuousLinearMap.fst ℝ ℝ (CoupledState E)

theorem norm_timeSpaceProjection_le : ‖timeSpaceProjection E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖(p.1, p.2.1)‖ ≤ 1 * ‖p‖
  rw [one_mul, Prod.norm_def]
  exact max_le (norm_fst_le p) ((norm_fst_le p.2).trans (norm_snd_le p))

/-- These are genuine preimage equalities, so no change of derivative domain
is hidden in the pullback argument. -/
theorem projection_preimage_openDomain :
    timeSpaceProjection E ⁻¹' openDomain E = openDomain (CoupledState E) := rfl

theorem projection_preimage_closedSlab (b : ℝ) :
    timeSpaceProjection E ⁻¹' closedSlab E b = closedSlab (CoupledState E) b := rfl

/-- The actual coupled field. Composition order is B.comp(U1), not U1.comp(B). -/
def velocity (r : ℝ) (M : ℝ × E → E) (U1 : ℝ × E → E →L[ℝ] E)
    (p : CoupledSpaceTime E) : CoupledState E :=
  ((-r) • M (p.1, p.2.1), (r * p.1) • p.2.2.comp (U1 (p.1, p.2.1)))

def liftedVelocity (r : ℝ) (M : ℝ × E → E) (U1 : ℝ × E → E →L[ℝ] E)
    (p : CoupledSpaceTime E) : CoupledSpaceTime E :=
  (1, velocity E r M U1 p)

variable {E}

theorem contDiffOn_velocity {r : ℝ}
    {M : ℝ × E → E} {U1 : ℝ × E → E →L[ℝ] E}
    (hM : ContDiffOn ℝ ∞ M (openDomain E))
    (hU1 : ContDiffOn ℝ ∞ U1 (openDomain E)) :
    ContDiffOn ℝ ∞ (velocity E r M U1) (openDomain (CoupledState E)) := by
  have hm : ContDiffOn ℝ ∞ (M ∘ timeSpaceProjection E)
      (openDomain (CoupledState E)) := hM.comp_continuousLinearMap _
  have hu : ContDiffOn ℝ ∞ (U1 ∘ timeSpaceProjection E)
      (openDomain (CoupledState E)) := hU1.comp_continuousLinearMap _
  have hb : ContDiffOn ℝ ∞ (matrixProjection E)
      (openDomain (CoupledState E)) := (matrixProjection E).contDiff.contDiffOn
  have hc : ContDiffOn ℝ ∞
      (fun p => (matrixProjection E p).comp ((U1 ∘ timeSpaceProjection E) p))
      (openDomain (CoupledState E)) :=
    (ContinuousLinearMap.compL ℝ E E E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hb hu
  have ht : ContDiffOn ℝ ∞ (timeCoefficient E r)
      (openDomain (CoupledState E)) := (timeCoefficient E r).contDiff.contDiffOn
  exact (contDiffOn_const.smul hm).prodMk (ht.smul hc)

theorem contDiffOn_liftedVelocity {r : ℝ}
    {M : ℝ × E → E} {U1 : ℝ × E → E →L[ℝ] E}
    (hM : ContDiffOn ℝ ∞ M (openDomain E))
    (hU1 : ContDiffOn ℝ ∞ U1 (openDomain E)) :
    ContDiffOn ℝ ∞ (liftedVelocity E r M U1) (openDomain (CoupledState E)) :=
  contDiffOn_const.prodMk (contDiffOn_velocity hM hU1)

/-- Exact finite-order supplier: order q of the lifted coupled velocity
uses only M/U1 bounds of orders i≤q. The spatial and B coordinates are
unrestricted on both the derivative domain and the bound slab. -/
theorem polynomialJetBound_liftedVelocity
    {b r : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {M : ℝ × E → E} {U1 : ℝ × E → E →L[ℝ] E}
    (hM : ContDiffOn ℝ ∞ M (openDomain E))
    (hU1 : ContDiffOn ℝ ∞ U1 (openDomain E)) (q : ℕ)
    (hMb : ∀ i ≤ q, PolynomialJetBound (openDomain E) (closedSlab E b) M i)
    (hUb : ∀ i ≤ q, PolynomialJetBound (openDomain E) (closedSlab E b) U1 i) :
    PolynomialJetBound (openDomain (CoupledState E)) (closedSlab (CoupledState E) b)
      (liftedVelocity E r M U1) q := by
  let U := openDomain (CoupledState E)
  let S := closedSlab (CoupledState E) b
  let m := M ∘ timeSpaceProjection E
  let u := U1 ∘ timeSpaceProjection E
  let a (p : CoupledSpaceTime E) :=
    (matrixProjection E p).comp (u p)
  have hU : UniqueDiffOn ℝ U := (isOpen_openDomain (CoupledState E)).uniqueDiffOn
  have hSU : S ⊆ U := closedSlab_subset_openDomain (CoupledState E) hb0 hb1
  have hm : ContDiffOn ℝ ∞ m U := hM.comp_continuousLinearMap _
  have hu : ContDiffOn ℝ ∞ u U := hU1.comp_continuousLinearMap _
  have hB : ContDiffOn ℝ ∞ (matrixProjection E) U :=
    (matrixProjection E).contDiff.contDiffOn
  have ht : ContDiffOn ℝ ∞ (timeCoefficient E r) U :=
    (timeCoefficient E r).contDiff.contDiffOn
  have ha : ContDiffOn ℝ ∞ a U :=
    (ContinuousLinearMap.compL ℝ E E E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hB hu
  have hmb : ∀ i ≤ q, PolynomialJetBound U S m i := by
    intro i hi
    exact polynomialJetBound_pullback (isOpen_openDomain E)
      (closedSlab_subset_openDomain E hb0 hb1) hM (timeSpaceProjection E)
      (norm_timeSpaceProjection_le E) i (hMb i hi)
  have hub : ∀ i ≤ q, PolynomialJetBound U S u i := by
    intro i hi
    exact polynomialJetBound_pullback (isOpen_openDomain E)
      (closedSlab_subset_openDomain E hb0 hb1) hU1 (timeSpaceProjection E)
      (norm_timeSpaceProjection_le E) i (hUb i hi)
  have hab : ∀ i ≤ q, PolynomialJetBound U S a i := by
    intro i hi
    exact polynomialJetBound_bilinear hU hSU
      (ContinuousLinearMap.compL ℝ E E E) (ContinuousLinearMap.norm_compL_le ℝ E E E)
      hB hu i
      (fun j _ => polynomialJetBound_linear hU hSU (matrixProjection E) j)
      (fun j hj => hub j (hj.trans hi))
  have hfirst : PolynomialJetBound U S (fun p => (-r) • m p) q :=
    polynomialJetBound_smul hU hSU contDiffOn_const hm q
      (fun i _ => polynomialJetBound_const U S (-r) i) hmb
  have hsecond : PolynomialJetBound U S
      (fun p => timeCoefficient E r p • a p) q :=
    polynomialJetBound_smul hU hSU ht ha q
      (fun i _ => polynomialJetBound_linear hU hSU (timeCoefficient E r) i) hab
  have hv : PolynomialJetBound U S (velocity E r M U1) q :=
    polynomialJetBound_prod hU hSU (contDiffOn_const.smul hm) (ht.smul ha)
      q hfirst hsecond
  exact polynomialJetBound_prod hU hSU contDiffOn_const
    (contDiffOn_velocity hM hU1) q (polynomialJetBound_const U S (1 : ℝ) q) hv

/-- Direct adapter to the velocity hypothesis of
ODEJet.exists_polynomial_stateJet_bound, with the strict q<K budget. -/
theorem exists_polynomial_liftedVelocity_bound
    {b r : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {M : ℝ × E → E} {U1 : ℝ × E → E →L[ℝ] E}
    (hM : ContDiffOn ℝ ∞ M (openDomain E))
    (hU1 : ContDiffOn ℝ ∞ U1 (openDomain E)) (K : ℕ)
    (hMb : ∀ i < K, PolynomialJetBound (openDomain E) (closedSlab E b) M i)
    (hUb : ∀ i < K, PolynomialJetBound (openDomain E) (closedSlab E b) U1 i) :
    ∀ q < K, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ p ∈ closedSlab (CoupledState E) b,
        ‖iteratedFDerivWithin ℝ q (fun z => ((1 : ℝ), velocity E r M U1 z))
          (openDomain (CoupledState E)) p‖ ≤ C * (1 + ‖p‖) ^ N := by
  intro q hq
  exact polynomialJetBound_liftedVelocity hb0 hb1 hM hU1 q
    (fun i hi => hMb i (hi.trans_lt hq))
    (fun i hi => hUb i (hi.trans_lt hq))
end Coupled
end AcceleratedLogConcave.Analysis.CoupledVelocityPolynomial
