import AcceleratedLogConcave.Oracle.FixedTapeMainState
import AcceleratedLogConcave.Oracle.NonterminalMeanValue

/-! Actual retained readout stability with explicit child induction hypotheses. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.FixedTapeStability
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation SourceMeanLayer RetainedMeanFinalBatch
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
/-- The retained correction cancels at identical parent/designated inputs. -/
theorem paidCorrection_sub_le (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (ef : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (slots : ∀ i, Fin (childSize (pf i)) → Fin C)
    (correctionSlots : Fin (1+(m+m)) → Fin C)
    (P : Ref Γ .point) (center designated : Fin m → Ref Γ .point)
    (outer : Origin) (auxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (T : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (cf i) → ℝ) (σ : ℝ) (w width : Fin m → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (env env' : Env d Γ)
    (htable : ∀ i, input.coefficient ∘ slots i = matrixTable (T i) (coeff i))
    (hcorrection : input.coefficient ∘ correctionSlots = RetainedMeanCorrection.table σ w width)
    (κ D : ℝ) (hκ : 0 ≤ κ) (hD0 : 0 ≤ D)
    (hchild : ∀ i, ChildStable (pf i) (coeff i) G κ)
    (hweights : ∑ i, |w i| ≤ 1)
    (hP : storedPoint env P = storedPoint env' P)
    (hdesignated : ∀ i, storedPoint env (designated i) = storedPoint env' (designated i))
    (hcenter : ∀ i, ‖storedPoint env (center i)-storedPoint env' (center i)‖ ≤ D)
    (tape : Tape d (paidCorrection cf pf ef slots correctionSlots P center designated outer auxiliary)) :
    ‖childPoint (run (paidCorrection cf pf ef slots correctionSlots P center designated outer auxiliary)
        G input env tape) -
      childPoint (run (paidCorrection cf pf ef slots correctionSlots P center designated outer auxiliary)
        G input env' tape)‖ ≤ κ*D := by
  rw [run_paidCorrection cf pf ef slots correctionSlots P center designated outer auxiliary
      σ w width G input env hcorrection,
    run_paidCorrection cf pf ef slots correctionSlots P center designated outer auxiliary
      σ w width G input env' hcorrection]
  dsimp only [childPoint,pointResult]
  have cancel (x y z : Point d) : x-z-(y-z) = x-y := by abel
  simp only [hP,hdesignated,add_sub_add_left_eq_sub,← Finset.sum_sub_distrib,
    ← smul_sub]
  simp only [cancel]
  have hc (i : Fin m) := (designatedChild_sub_le (pf i) (ef i) (slots i) (center i)
    (designated i) (auxiliary i) (T i) (coeff i) G input env env' (htable i)
    (hdesignated i) κ (hchild i) (tape.1 i)).trans (mul_le_mul_of_nonneg_left (hcenter i) hκ)
  simpa only [one_mul,childPoint] using Numerics.AffineGraph.norm_sum_smul_le_of_norm_le w
    (fun i => childPoint (run (designatedChild (pf i) (ef i) (slots i) (center i)
      (designated i) (auxiliary i)) G input env (tape.1 i)) -
      childPoint (run (designatedChild (pf i) (ef i) (slots i) (center i)
      (designated i) (auxiliary i)) G input env' (tape.1 i))) hweights
    (mul_nonneg hκ hD0) hc

section Loop
variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ .point)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (κ a B : ℝ)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hB0 : 0 ≤ B)
    (htable : ∀ i, input.coefficient ∘ (slots ∘ childSlot c p i) = matrixTable (T i) (coeff i))
    (hchild : ∀ i, ChildStable (p i) (coeff i) G κ)
    (hrow : ∀ i, ∑ j, |input.coefficient (slots (aSlot c p i j))| ≤ a)
    (P : Ref Ξ .point) (kept : Fin m → Ref Ξ .point) (L : ℝ)
    (hfinish : ∀ {Δ : Ctx} (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ)
      (env env' : Env d Δ) (tape : Tape d (finish old direct saved)) (D : ℝ),
      0 ≤ D → (∀ i, ‖storedPoint env (old i)-storedPoint env' (old i)‖ ≤ D) →
      storedPoint env (saved P) = storedPoint env' (saved P) →
      (∀ i, storedPoint env (saved (kept i)) = storedPoint env' (saved (kept i))) →
      ‖childPoint (run (finish old direct saved) G input env tape) -
        childPoint (run (finish old direct saved) G input env' tape)‖ ≤ L*D)
include hκ ha hB0 htable hchild hrow hfinish

/-- Synchronize the literal tail tape at each successor, without comparing traces. -/
theorem iterateThen_sub_le_growth (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (env env' : Env d Γ)
    (tape : Tape d (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved))
    (D0 : ℝ) (hD0 : 0 ≤ D0)
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (hD : ∀ i, ‖storedPoint env (old i)-storedPoint env' (old i)‖ ≤ D0)
    (hP : storedPoint env (saved P) = storedPoint env' (saved P))
    (hkept : ∀ i, storedPoint env (saved (kept i)) = storedPoint env' (saved (kept i))) :
    ‖childPoint (run (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved)
      G input env tape) -
      childPoint (run (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved)
      G input env' tape)‖ ≤ L*growth (κ*a) B D0 N := by
  induction N generalizing Γ D0 with
  | zero => exact hfinish old direct saved env env' tape D0 hD0 hD hP hkept
  | succ N ih =>
    let Q := fun i => childPoint (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
      (old i) (designated N i) (auxiliary N i)) G input env (tape.1 i))
    let Q' := fun i => childPoint (run (freshChild (p i) (e i) (slots ∘ childSlot c p i)
      (old i) (designated N i) (auxiliary N i)) G input env' (tape.1 i))
    let Z := fun i => (tape.2.1 i).1
    let X := noisyValues (fun i j => slots (aSlot c p i j))
      (fun i j => slots (residualSlot c p i j)) direct input env Q Z
    let X' := noisyValues (fun i j => slots (aSlot c p i j))
      (fun i j => slots (residualSlot c p i j)) direct input env' Q' Z
    have hQ (i : Fin n) : ‖Q i-Q' i‖ ≤ κ*D0 :=
      (freshChild_sub_le (p i) (e i) (slots ∘ childSlot c p i) (old i)
        (designated N i) (auxiliary N i) (T i) (coeff i) G input env env'
        (htable i) κ (hchild i) (tape.1 i)).trans (mul_le_mul_of_nonneg_left (hD i) hκ)
    have hX (i : Fin n) : ‖X i-X' i‖ ≤ κ*a*D0+B := by
      have h := noisyValues_sub_le (fun i j => slots (aSlot c p i j))
        (fun i j => slots (residualSlot c p i j)) direct input env env' Q Q' Z a B (κ*D0)
        (mul_nonneg hκ hD0) hrow hB hQ i
      convert h using 1
      ring
    have hs (r : Ref Ξ .point) :
        storedPoint (Env.prepend X (Env.prepend Z (Env.prepend Q env))) (preserveDirect (saved r)) =
          storedPoint env (saved r) := stored_preserveDirect env Q Z X (saved r)
    have hs' (r : Ref Ξ .point) :
        storedPoint (Env.prepend X' (Env.prepend Z (Env.prepend Q' env'))) (preserveDirect (saved r)) =
          storedPoint env' (saved r) := stored_preserveDirect env' Q' Z X' (saved r)
    have hi := ih batchRef (fun j => preserveDirect (direct j))
      (fun r => preserveDirect (saved r))
      (Env.prepend X (Env.prepend Z (Env.prepend Q env)))
      (Env.prepend X' (Env.prepend Z (Env.prepend Q' env'))) tape.2.2.2
      (κ*a*D0+B) (by positivity)
      (fun i => by
        rw [stored_preserveDirect env Q Z X,stored_preserveDirect env' Q' Z X']
        exact hB i)
      (fun i => by simpa only [prepend_batchRef] using hX i)
      (by rw [hs,hs']; exact hP) (fun i => by rw [hs,hs']; exact hkept i)
    dsimp only [iterateThen] at tape ⊢
    rw [run_layerAt,run_layerAt]
    simpa only [growth_shift,Q,Q',X,X',Z,childPoint] using hi
end Loop

section Block
variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (mainSlots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (cf : Fin m → ℕ) (pf : ∀ i, Program (cf i) .point)
    (ef : ∀ i, GaussianSlot (pf i) ≃ Fin (tapeShape (pf i)).gaussianBlocks)
    (finalSlots : ∀ i, Fin (childSize (pf i)) → Fin C)
    (correctionSlots : Fin (1+(m+m)) → Fin C) (rhoSlot : Fin C)
    (P : Ref Γ .point) (designatedFinal : Fin m → Ref Γ .point)
    (direct : Fin n → Ref Γ .point) (active : Fin m → Fin n)
    (initialOrigin : Fin n → Origin) (outer : ℕ → Origin)
    (mainDesignated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finalOuter : Origin)
    (finalAuxiliary : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Origin)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ)
    (Tf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeffF : ∀ i, Fin (cf i) → ℝ)
    (σ : ℝ) (w width : Fin m → ℝ)
    (G : Point d → Point d) (input : Inputs d C) (κ a B : ℝ)
    (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hB0 : 0 ≤ B)
    (htable : ∀ i, input.coefficient ∘ (mainSlots ∘ childSlot c p i) = matrixTable (T i) (coeff i))
    (hchild : ∀ i, ChildStable (p i) (coeff i) G κ)
    (hrow : ∀ i, ∑ j, |input.coefficient (mainSlots (aSlot c p i j))| ≤ a)
    (htableF : ∀ i, input.coefficient ∘ finalSlots i = matrixTable (Tf i) (coeffF i))
    (hchildF : ∀ i, ChildStable (pf i) (coeffF i) G κ)
    (hcorrection : input.coefficient ∘ correctionSlots = RetainedMeanCorrection.table σ w width)
    (hweights : ∑ i, |w i| ≤ 1)
include hκ ha hB0 htable hchild hrow htableF hchildF hcorrection hweights

/-- Actual initialized main block and paid final children on one literal raw tape. -/
theorem code_sub_le_growth (N : ℕ) (env env' : Env d Γ)
    (hP : storedPoint env P = storedPoint env' P)
    (hdesignated : ∀ i, storedPoint env (designatedFinal i) = storedPoint env' (designatedFinal i))
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (tape : Tape d (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N)) :
    ‖childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N) G input env tape) -
      childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N) G input env' tape)‖ ≤ κ*growth (κ*a) B B N := by
  let finish := fun {Δ : Ctx} (old _ : Fin n → Ref Δ .point) (saved : RefMap Γ Δ) =>
    paidCorrection cf pf ef finalSlots correctionSlots (saved P)
      (fun i => old (active i)) (fun i => saved (designatedFinal i)) finalOuter finalAuxiliary
  have hf : ∀ {Δ : Ctx} (old dir : Fin n → Ref Δ .point) (saved : RefMap Γ Δ)
      (ρ ρ' : Env d Δ) (tail : Tape d (finish old dir saved)) (D : ℝ),
      0 ≤ D → (∀ i, ‖storedPoint ρ (old i)-storedPoint ρ' (old i)‖ ≤ D) →
      storedPoint ρ (saved P) = storedPoint ρ' (saved P) →
      (∀ i, storedPoint ρ (saved (designatedFinal i)) = storedPoint ρ' (saved (designatedFinal i))) →
      ‖childPoint (run (finish old dir saved) G input ρ tail) -
        childPoint (run (finish old dir saved) G input ρ' tail)‖ ≤ κ*D := by
    intro Δ old dir saved ρ ρ' tail D hD hd hp hpi
    exact paidCorrection_sub_le cf pf ef finalSlots correctionSlots (saved P)
      (fun i => old (active i)) (fun i => saved (designatedFinal i)) finalOuter finalAuxiliary
      Tf coeffF σ w width G input ρ ρ' htableF hcorrection κ D hκ hD hchildF hweights hp hpi
      (fun i => hd (active i)) tail
  let Z : Fin n → Point d := fun i => (tape.1 i).1
  let X := fun i => storedPoint env (direct i)+input.coefficient rhoSlot • Z i
  let X' := fun i => storedPoint env' (direct i)+input.coefficient rhoSlot • Z i
  let ρ : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend X (Env.prepend Z env)
  let ρ' : Env d (replyCtx n (replyCtx n Γ)) := Env.prepend X' (Env.prepend Z env')
  have hs (r : Ref Γ .point) :
      storedPoint ρ (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env r := by
    exact (prepend_shiftMany X (Env.prepend Z env) (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env r)
  have hs' (r : Ref Γ .point) :
      storedPoint ρ' (RefMap.shiftMany n (RefMap.shiftMany n r)) = storedPoint env' r := by
    exact (prepend_shiftMany X' (Env.prepend Z env') (RefMap.shiftMany n r)).trans
      (prepend_shiftMany Z env' r)
  have hi := iterateThen_sub_le_growth c p mainSlots e outer mainDesignated residual auxiliary
    finish T coeff G input κ a B hκ ha hB0 htable hchild hrow P designatedFinal κ hf
    N batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r)) ρ ρ' tape.2.2 B hB0
    (fun i => by rw [hs,hs']; exact hB i)
    (fun i => by simpa only [ρ,ρ',prepend_batchRef,X,X',add_sub_add_right_eq_sub] using hB i)
    (by rw [hs,hs']; exact hP) (fun i => by rw [hs,hs']; exact hdesignated i)
  dsimp only [NonterminalMeanBlock.code] at tape ⊢
  rw [run_initialize,run_initialize]
  exact hi

/-- Initialization contributes B, hence the inclusive finite sum through N. -/
theorem code_sub_le (N : ℕ) (env env' : Env d Γ)
    (hP : storedPoint env P = storedPoint env' P)
    (hdesignated : ∀ i, storedPoint env (designatedFinal i) = storedPoint env' (designatedFinal i))
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (tape : Tape d (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N)) :
    ‖childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N) G input env tape) -
      childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N) G input env' tape)‖ ≤ κ*B*∑ j ∈ Finset.range (N+1), (κ*a)^j := by
  have h := code_sub_le_growth c p mainSlots e cf pf ef finalSlots correctionSlots rhoSlot P
    designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary finalOuter
    finalAuxiliary T coeff Tf coeffF σ w width G input κ a B hκ ha hB0 htable hchild hrow
    htableF hchildF hcorrection hweights N env env' hP hdesignated hB tape
  calc
    _ ≤ κ*growth (κ*a) B B N := h
    _ ≤ κ*((κ*a)^N*B+B*∑ j ∈ Finset.range N, (κ*a)^j) :=
      mul_le_mul_of_nonneg_left (growth_le (κ*a) B B (mul_nonneg hκ ha) N) hκ
    _ = _ := by rw [Finset.sum_range_succ]; ring

/-- Geometric bound for the actual code, with q < 1 kept explicit. -/
theorem code_sub_le_geometric (N : ℕ) (env env' : Env d Γ)
    (hP : storedPoint env P = storedPoint env' P)
    (hdesignated : ∀ i, storedPoint env (designatedFinal i) = storedPoint env' (designatedFinal i))
    (hB : ∀ i, ‖storedPoint env (direct i)-storedPoint env' (direct i)‖ ≤ B)
    (hq : κ*a < 1)
    (tape : Tape d (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N)) :
    ‖childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N) G input env tape) -
      childPoint (run (NonterminalMeanBlock.code c p mainSlots e cf pf ef finalSlots correctionSlots
      rhoSlot P designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary
      finalOuter finalAuxiliary N) G input env' tape)‖ ≤ κ*B/(1-κ*a) := by
  have h := code_sub_le c p mainSlots e cf pf ef finalSlots correctionSlots rhoSlot P
    designatedFinal direct active initialOrigin outer mainDesignated residual auxiliary finalOuter
    finalAuxiliary T coeff Tf coeffF σ w width G input κ a B hκ ha hB0 htable hchild hrow
    htableF hchildF hcorrection hweights N env env' hP hdesignated hB tape
  have hs : ∑ j ∈ Finset.range (N+1), (κ*a)^j ≤ (1-κ*a)⁻¹ := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N+1) (mul_nonneg hκ ha) hq)
  exact h.trans (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hs (mul_nonneg hκ hB0))
end Block

end AcceleratedLogConcave.Oracle.FixedTapeStability
