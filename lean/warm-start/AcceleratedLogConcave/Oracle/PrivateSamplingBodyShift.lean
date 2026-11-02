import AcceleratedLogConcave.Oracle.PrivateSamplingShift

noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateSamplingProgram
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open ChildAbsorption CovarianceSetup LayerShift ExecutableShiftWeights SourceExecutableShift

set_option backward.isDefEq.respectTransparency false in
/-- Actual initialization followed by every finite sampling layer. Initial
center-residual Gaussians stay fixed; the entire Result trace is preserved. -/
theorem body_translation {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (outputDirect : Ref Γ .point) (rho r Ds : ℝ) (radius k : Fin n → ℝ)
    (vm : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (vf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (cm : ∀ i, Fin (c i) → ℝ) (cfinal : ∀ i, Fin (cf i) → ℝ)
    (hm : ∀ i, Admissible rho (radius i) Ds (vm i))
    (hf : ∀ i, Admissible rho (radius i) Ds (vf i)) (hr : 0 < r)
    (hsm : ∀ i, QueryShift (p i) (cfg.mainEquiv i) (cm i) (radius i) (vm i))
    (hsf : ∀ i, QueryShift (pf i) (cfg.finalEquiv i) (cfinal i) (radius i) (vf i))
    (G : Point d → Point d) (input input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient) (Δ : Point d) (a reserveShift : ℝ)
    (htm : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) =
      matrixTable (childRoot rho (radius i) (vm i)) (cm i))
    (htf : ∀ i, input.coefficient ∘ cfg.finalSlots i =
      matrixTable (childRoot rho (radius i) (vf i)) (cfinal i))
    (direct : Fin n → Ref Γ .point) (env env' : Env d Γ)
    (hdir : ∀ i, storedPoint env' (direct i) = storedPoint env (direct i) + k i • Δ)
    (hout : storedPoint env' outputDirect = storedPoint env outputDirect + a • Δ)
    (tape : Tape d (body cfg direct outputDirect)) :
    run (body cfg direct outputDirect) G input' env'
      (translate (body cfg direct outputDirect)
        (samplingBody cfg direct outputDirect
          (fun i => rawShift rho (radius i) r (k i) (vm i))
          (fun i => rawShift rho (radius i) r (k i) (vf i)) reserveShift) r Δ tape) =
      displaced (run (body cfg direct outputDirect) G input env tape)
        (a + input.coefficient cfg.reserve * (reserveShift/r)) Δ := by
  let shifted := translate (body cfg direct outputDirect)
    (samplingBody cfg direct outputDirect
      (fun i => rawShift rho (radius i) r (k i) (vm i))
      (fun i => rawShift rho (radius i) r (k i) (vf i)) reserveShift) r Δ tape
  let Z : Fin n → Point d := fun i => (tape.1 i).1
  have hz : (fun i : Fin n => (shifted.1 i).1) = Z := by
    funext i
    change (show Point d from (tape.1 i).1) + (0/r) • Δ = _
    simp only [zero_div,zero_smul,add_zero]
    rfl
  let X : Fin n → Point d := fun i =>
    storedPoint env (direct i) + input.coefficient cfg.noise • Z i
  let X' : Fin n → Point d := fun i =>
    storedPoint env' (direct i) + input'.coefficient cfg.noise • Z i
  have hx (i : Fin n) : X' i = X i + k i • Δ := by
    simp only [X',X,hcoeff,hdir]
    abel
  have hs (r : Ref Γ .point) :
      Env.prepend X' (Env.prepend Z env') (RefMap.shiftMany n (RefMap.shiftMany n r)) = env' r :=
    (prepend_shiftMany X' _ _).trans (prepend_shiftMany Z _ _)
  have hb (r : Ref Γ .point) :
      Env.prepend X (Env.prepend Z env) (RefMap.shiftMany n (RefMap.shiftMany n r)) = env r :=
    (prepend_shiftMany X _ _).trans (prepend_shiftMany Z _ _)
  have hl := loop_translation cfg outputDirect rho r Ds radius k vm vf cm cfinal
    hm hf hr hsm hsf G input input' hcoeff Δ a reserveShift htm htf cfg.layers
    batchRef (fun i => RefMap.shiftMany n (RefMap.shiftMany n (direct i)))
    (fun r => RefMap.shiftMany n (RefMap.shiftMany n r))
    (Env.prepend X (Env.prepend Z env)) (Env.prepend X' (Env.prepend Z env'))
    (fun i => (prepend_batchRef X' _ i).trans
      ((hx i).trans (congrArg (fun z => z + k i • Δ) (prepend_batchRef X _ i).symm)))
    (fun i => (hs (direct i)).trans
      ((hdir i).trans (congrArg (fun z => z + k i • Δ) (hb (direct i)).symm)))
    ((hs outputDirect).trans
      (hout.trans (congrArg (fun z => z + a • Δ) (hb outputDirect).symm))) tape.2.2
  have ht := run_body cfg direct outputDirect G input' env' shifted
  have hu := run_body cfg direct outputDirect G input env tape
  dsimp only at ht hu hl
  have hrow : (fun j => storedPoint env' (direct j) +
      input'.coefficient cfg.noise • (show Point d from (shifted.1 j).1)) = X' :=
    funext (fun j => congrArg (fun z => storedPoint env' (direct j) +
      input'.coefficient cfg.noise • z) (congrFun hz j))
  erw [hrow,hz] at ht
  change run (body cfg direct outputDirect) G input' env' shifted = _
  rw [ht,hu]
  erw [hl]
  rfl

end AcceleratedLogConcave.Oracle.PrivateSamplingProgram
