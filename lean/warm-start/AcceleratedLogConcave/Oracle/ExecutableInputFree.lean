import AcceleratedLogConcave.Oracle.NoisyLayer

noncomputable section
namespace AcceleratedLogConcave.Oracle.NoisyLayer
open TapeLowering AffineLowering

/-- A child embedding reads its stored center and fresh designated input. Its
host's external center and momentum are therefore irrelevant to the full Result. -/
theorem freshChild_same_coefficients (p : Program c .point)
    (e : GaussianSlot p ≃ Fin N) (slots : Fin (N*N+c) → Fin C)
    (old : Ref Γ .point) (designated : Origin) (auxiliary : Fin N → Origin)
    (T : Fin N → Fin N → ℝ) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (input input' : Inputs d C) (env : Env d Γ)
    (hcoeff : input'.coefficient = input.coefficient)
    (htable : input.coefficient ∘ slots = matrixTable T coeff)
    (tape : Tape d (freshChild p e slots old designated auxiliary)) :
    run (freshChild p e slots old designated auxiliary) G input' env tape =
      run (freshChild p e slots old designated auxiliary) G input env tape := by
  have ht' : input'.coefficient ∘ slots = matrixTable T coeff := by rw [hcoeff,htable]
  exact (run_freshChild p e slots old designated auxiliary T coeff G input' env ht' tape).trans
    (run_freshChild p e slots old designated auxiliary T coeff G input env htable tape).symm

end AcceleratedLogConcave.Oracle.NoisyLayer
