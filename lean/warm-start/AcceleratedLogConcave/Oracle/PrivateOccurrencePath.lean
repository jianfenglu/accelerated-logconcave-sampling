import AcceleratedLogConcave.Oracle.TailOccurrenceCut
import AcceleratedLogConcave.Oracle.PrivatePrefixWrapper

/-! Occurrence paths on the original source syntax. These traverse
continuations, never a fresh independent execution or a renumbered short loop. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.TailOccurrenceCut
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer RecursiveMeanProgram
open RecursiveMeanContinuation PrivateSamplingProgram SourceExecutableTables

structure Focused {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) where
  ctx : Ctx
  code : Prog c ctx τ
  cut : TailCut code p

variable (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (slots : Fin (publicSize c p) → Fin C)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
    (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
      (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)

def atLayer : (N k : ℕ) → {Γ : Ctx} →
    (old direct : Fin n → Ref Γ .point) → (saved : RefMap Ξ Γ) →
    Focused (iterateThen c p slots e outer designated residual auxiliary finish N old direct saved)
  | _N, 0, Γ, _old, _direct, _saved => ⟨Γ,_,.here⟩
  | 0, _+1, Γ, _old, _direct, _saved => ⟨Γ,_,.here⟩
  | N+1, k+1, _, old, direct, saved =>
      let f := atLayer N k batchRef (fun j => preserveDirect (direct j))
        (fun r => preserveDirect (saved r))
      ⟨f.ctx, f.code,
        .batch (outer N)
          (fun i => freshChild (p i) (e i) (slots ∘ childSlot c p i)
            (old i) (designated N i) (auxiliary N i)) _
          (.batch [] (fun i => residualDraw (residual N i)) _
            (.batch [] (noisyRow (fun j k => slots (aSlot c p j k))
              (fun j k => slots (residualSlot c p j k)) direct) _ f.cut))⟩

/-- Four actual setup instructions, then the direct-row batch and the two
initialization batches. The focus at k<N is the next main child batch. -/
def privateAtLayer {m n : ℕ} (S : Numerics.AffineGraph.SamplingGeometry m)
    (nodes : Fin n ≃ S.Node) (r Ds : ℝ) (main final : Fin n → ExecutableData)
    (N k : ℕ) : Focused (SamplingExecutable.build S nodes r Ds main final N).program := by
  let cfg := samplingConfig main final N
  let f := atLayer (fun i => (main i).size) (fun i => (main i).program)
    cfg.mainSlots (fun i => (main i).enumeration) cfg.layerOrigin cfg.mainDesignated
    cfg.mainResidual cfg.mainAuxiliary (PrivateSamplingExecutionSchedule.finisher main final N)
    N k batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
    (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
  refine ⟨f.ctx, f.code, ?_⟩
  change TailCut f.code (PrivateSamplingProgram.code cfg)
  unfold PrivateSamplingProgram.code PrivateSamplingProgram.body initializeCenters
  exact .step _ _ _ (.step _ _ _ (.step _ _ _ (.step _ _ _
    (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ f.cut))))))

end AcceleratedLogConcave.Oracle.TailOccurrenceCut
