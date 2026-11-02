import AcceleratedLogConcave.Oracle.ExecutableShiftWeights
import AcceleratedLogConcave.Oracle.ExecutableData

/-! Exact squared-mass accounting over the actual structural Gaussian slots.
Lowering and raw compiler routing do not duplicate or remove a nonzero weight.
The local finite sums count each executed child occurrence separately. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.ExecutableShiftMass
open TapeLowering AffineLowering NoisyLayer ExecutableShiftWeights CovarianceSetup
open scoped BigOperators

/-- Squared Euclidean block-index norm on the actual program Gaussian slots. -/
def slotMass (p : Prog c Γ τ) (w : GaussianSlot p → ℝ) : ℝ := ∑ s, (w s)^2

@[simp] theorem slotMass_zero (p : Prog c Γ τ) : slotMass p (fun _ => 0) = 0 := by
  simp [slotMass]

/-- Full fixed enumeration has exactly the same mass as structural source slots. -/
theorem shiftVector_mass (data : ExecutableData) :
    shiftSq data.shiftVector = slotMass data.program data.shift := by
  unfold shiftSq ExecutableData.shiftVector slotMass
  exact data.enumeration.symm.sum_comp (fun s => (data.shift s)^2)

/-- Exact disjoint sum of instruction and continuation Gaussian-slot masses. -/
theorem slotMass_step (origin : Origin) (instr : Instr c Γ σ)
    (next : Prog c (σ :: Γ) τ) (w : GaussianSlot (.step origin instr next) → ℝ) :
    slotMass (.step origin instr next) w =
      (∑ s : InstrGaussianSlot instr, (w (.inl s))^2) +
      slotMass next (fun s => w (.inr s)) := by
  exact Fintype.sum_sum_type _

/-- Every child occurrence and the continuation occupy disjoint actual slots. -/
theorem slotMass_batch (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (replyCtx n Γ) τ)
    (w : GaussianSlot (.batch origin children next) → ℝ) :
    slotMass (.batch origin children next) w =
      (∑ j, slotMass (children j) (fun s => w (.inl ⟨j,s⟩))) +
      slotMass next (fun s => w (.inr s)) := by
  unfold slotMass
  change (∑ s : (Σ j, GaussianSlot (children j)) ⊕ GaussianSlot next, (w s)^2) = _
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]

/-- Literal coefficient/reference lowering preserves the entire squared mass. -/
theorem lowerWeights_mass (κ : Fin c → Fin c') (p : Prog c Γ τ)
    (f : RefMap Γ Ξ) (center momentum : Ref Ξ .point) (w : GaussianSlot p → ℝ) :
    slotMass (p.lower κ f center momentum) (lowerWeights κ p f center momentum w) =
      slotMass p w := by
  induction p generalizing Ξ with
  | ret a =>
      change (∑ s : PEmpty, _) = ∑ s : PEmpty, _
      simp only [Fintype.sum_empty]
  | step origin instr next ih =>
      cases instr with
      | pure a =>
          simp only [Prog.lower]
          erw [slotMass_step,slotMass_step]
          change (∑ s : PEmpty, _) + slotMass _ (lowerWeights κ next f.lift
            (.there center) (.there momentum) (fun s => w (.inr s))) =
            (∑ s : PEmpty, _) + slotMass next (fun s => w (.inr s))
          simp only [Fintype.sum_empty,zero_add]
          exact ih _ _ _ _
      | center =>
          change slotMass _ (lowerWeights κ next (f.bind center) center momentum
            (fun s => w (.inr s))) = slotMass _ w
          rw [ih,slotMass_step]
          change _ = (∑ s : PEmpty, _) + _
          simp only [Fintype.sum_empty,zero_add]
      | momentum =>
          change slotMass _ (lowerWeights κ next (f.bind momentum) center momentum
            (fun s => w (.inr s))) = slotMass _ w
          rw [ih,slotMass_step]
          change _ = (∑ s : PEmpty, _) + _
          simp only [Fintype.sum_empty,zero_add]
      | grad v =>
          simp only [Prog.lower]
          erw [slotMass_step,slotMass_step]
          change (∑ s : PEmpty, _) + slotMass _ (lowerWeights κ next f.lift
            (.there center) (.there momentum) (fun s => w (.inr s))) =
            (∑ s : PEmpty, _) + slotMass next (fun s => w (.inr s))
          simp only [Fintype.sum_empty,zero_add]
          exact ih _ _ _ _
      | gaussian =>
          simp only [Prog.lower]
          erw [slotMass_step,slotMass_step]
          change (∑ s : PUnit, (w (.inl s))^2) + slotMass _ (lowerWeights κ next f.lift
            (.there center) (.there momentum) (fun s => w (.inr s))) =
            (∑ s : PUnit, (w (.inl s))^2) + slotMass next (fun s => w (.inr s))
          rw [ih]
      | uniform =>
          simp only [Prog.lower]
          erw [slotMass_step,slotMass_step]
          change (∑ s : PEmpty, _) + slotMass _ (lowerWeights κ next f.lift
            (.there center) (.there momentum) (fun s => w (.inr s))) =
            (∑ s : PEmpty, _) + slotMass next (fun s => w (.inr s))
          simp only [Fintype.sum_empty,zero_add]
          exact ih _ _ _ _
  | batch origin children next ihc ihn =>
      simp only [Prog.lower]
      erw [slotMass_batch,slotMass_batch]
      have hs (j) := ihc j f center momentum (fun s => w (.inl ⟨j,s⟩))
      have ht := ihn (f.liftMany _) (RefMap.shiftMany _ center) (RefMap.shiftMany _ momentum)
        (fun s => w (.inr s))
      simp only [lowerWeights,Function.comp_def] at hs ht
      simp only [lowerWeights,Function.comp_def,lowerSlot]
      rw [ht]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact hs j

/-- The single raw draw contributes precisely its one supplied weight. -/
theorem rawDraw_mass (origin : Origin) (a : ℝ) :
    slotMass (rawDraw (c := c) origin)
      (fun s => match s with | .inl _ => a | .inr t => nomatch t) = a^2 := by
  change (∑ s : PUnit.{1} ⊕ PEmpty.{1},
    (match s with | .inl _ => a | .inr t => nomatch t)^2) = _
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,Fintype.sum_empty,add_zero]

set_option maxHeartbeats 1000000 in
/-- Compiler presampling puts each raw block weight in precisely one slot. -/
theorem compiledWeights_mass (p : Program c τ) (e : GaussianSlot p ≃ Fin N)
    (auxiliary : Fin N → Origin) (w : Fin N → ℝ) :
    slotMass (compileWith p e auxiliary) (compiledWeights p e auxiliary w) = shiftSq w := by
  unfold compileWith
  erw [slotMass_step,slotMass_step,slotMass_batch]
  simp only [compiledWeights]
  change (∑ _s : PEmpty, (0:ℝ)^2) + ((∑ _s : PEmpty, (0:ℝ)^2) +
    ((∑ j, slotMass (rawDraw (c := N*N+c) (auxiliary j))
      (fun s => match s with | .inl _ => w j | .inr t => nomatch t)) +
      slotMass _ (fun _ => 0))) = shiftSq w
  rw [slotMass_zero]
  simp only [Fintype.sum_empty,add_zero,zero_add]
  unfold shiftSq
  apply Finset.sum_congr rfl
  intro j _
  exact rawDraw_mass (c := N*N+c) (auxiliary j) (w j)

/-- A fresh designated Gaussian has zero weight; the entire mass is exactly
its separate raw auxiliary batch mass, without a cost/inventory discount. -/
theorem freshWeights_mass (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (slots : Fin (N*N+c) → Fin C) (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin) (w : Fin N → ℝ) :
    slotMass (freshChild p e slots old designated auxiliary)
      (freshWeights p e slots old designated auxiliary w) = shiftSq w := by
  unfold freshChild
  erw [slotMass_step]
  change (∑ _s : PUnit, (0:ℝ)^2) +
    slotMass _ (lowerWeights slots (compileWith p e auxiliary) (fun r => nomatch r)
      (.there old) .here (compiledWeights p e auxiliary w)) = _
  rw [lowerWeights_mass,compiledWeights_mass]
  simp only [zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_add]


/-- Typed batch assembly adds the masses of its actual disjoint slot families. -/
theorem batchWeights_mass (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (replyCtx n Γ) τ) (child : ∀ i, GaussianSlot (children i) → ℝ)
    (tail : GaussianSlot next → ℝ) :
    slotMass (.batch origin children next) (Sum.elim (fun s => child s.1 s.2) tail) =
      (∑ i, slotMass (children i) (child i)) + slotMass next tail := by
  erw [slotMass_batch]
  rfl

/-- Held-fixed batches retain all their slots while contributing zero mass. -/
theorem batchZero_mass (origin : Origin) (children : Fin n → Prog c Γ .point)
    (next : Prog c (replyCtx n Γ) τ) (tail : GaussianSlot next → ℝ) :
    slotMass (.batch origin children next) (Sum.elim (fun _ => 0) tail) = slotMass next tail := by
  erw [slotMass_batch]
  change (∑ i, slotMass (children i) (fun _ => 0)) + slotMass next tail = _
  simp only [slotMass_zero,Finset.sum_const_zero,zero_add]

/-- Exact source-layer mass, including each fresh child occurrence once. -/
theorem layerWeights_mass (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog C (nextCtx n Γ) τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (tail : GaussianSlot next → ℝ) :
    slotMass (SourceMeanLayer.layerAt c p slots e old direct outer designated residual auxiliary next)
      (layerWeights c p slots e old direct outer designated residual auxiliary next w tail) =
      (∑ i, shiftSq (w i)) + slotMass next tail := by
  unfold SourceMeanLayer.layerAt layerWeights
  erw [slotMass_batch]
  change (∑ i, slotMass
    (freshChild (p i) (e i) (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i))
    (freshWeights (p i) (e i) (slots ∘ childSlot c p i) (old i) (designated i) (auxiliary i) (w i))) +
    slotMass (.batch [] (fun i => residualDraw (residual i))
      (.batch [] (noisyRow (fun j k => slots (aSlot c p j k))
        (fun j k => slots (residualSlot c p j k)) direct) next))
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) tail)) = _
  erw [batchZero_mass,batchZero_mass]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact freshWeights_mass (p i) (e i) (slots ∘ childSlot c p i) (old i)
    (designated i) (auxiliary i) (w i)

/-- Actual initialization contributes zero shift mass, including all initial
center-residual draws and the entire stored-row batch. -/
theorem initializeWeights_mass (rho : Fin C) (direct : Fin n → Ref Γ .point)
    (outer : Origin) (origin : Fin n → Origin)
    (next : Prog C (noiseCtx n Γ) τ) (tail : GaussianSlot next → ℝ) :
    slotMass (initializeCenters rho direct outer origin next)
      (initializeWeights rho direct outer origin next tail) = slotMass next tail := by
  unfold initializeCenters initializeWeights
  erw [batchZero_mass,batchZero_mass]

/-- Exact finite-loop mass identity. The local endpoint premise only computes
the finish syntax's mass; it assumes no recursive norm budget or QueryShift. -/
theorem iterateWeights_mass (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (finishWeights : ∀ {Δ : Ctx} (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ),
      GaussianSlot (finish old direct saved) → ℝ)
    (finishMass : ℝ)
    (hfinish : ∀ {Δ : Ctx} (old direct : Fin n → Ref Δ .point) (saved : RefMap Ξ Δ),
      slotMass (finish old direct saved) (finishWeights old direct saved) = finishMass)
    (N : ℕ) {Γ : Ctx} (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) :
    slotMass (RecursiveMeanContinuation.iterateThen c p slots e outer designated residual
      auxiliary finish N old direct saved)
      (iterateWeights c p slots e outer designated residual auxiliary finish w finishWeights
        N old direct saved) = (N:ℝ) * (∑ i, shiftSq (w i)) + finishMass := by
  induction N generalizing Γ with
  | zero => simpa only [iterateWeights,RecursiveMeanContinuation.iterateThen,
      Nat.cast_zero,zero_mul,zero_add] using hfinish old direct saved
  | succ N ih =>
      rw [iterateWeights]
      erw [layerWeights_mass,ih]
      push_cast
      ring


end AcceleratedLogConcave.Oracle.ExecutableShiftMass
