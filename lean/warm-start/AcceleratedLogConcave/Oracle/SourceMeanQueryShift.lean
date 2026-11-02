import AcceleratedLogConcave.Oracle.SourceMeanBodyShift
import AcceleratedLogConcave.Oracle.PrivateSamplingProgramShift
import AcceleratedLogConcave.Oracle.SamplingExecutable

/-! Full nonterminal source mean query shift. Every premise concerns actual
smaller mean programs or source scalar geometry; no parent execution or trace
invariant is assumed. The paid private sampler uses its computed reserve shift. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceMeanQueryShift
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open ChildAbsorption ExecutableShiftWeights SourceMeanShift

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
theorem queryShift (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (smain sfinal : Fin ns → ExecutableData) (layers : ℕ) (hr : 0 < r)
    (hτ : S.τ = M.R / backwardEnd M.R)
    (hm : ∀ i, Admissible (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (M.radius r (nodes i)) Ds (main i).shiftVector)
    (hsm : ∀ i, QueryShift (main i).program (main i).enumeration
      (main i).coefficient (M.radius r (nodes i)) (main i).shiftVector)
    (hpm : ∀ i, Admissible (SourceExecutableTables.samplingNoise S r Ds)
      (S.radius r (snodes i)) Ds (smain i).shiftVector)
    (hpf : ∀ i, Admissible (SourceExecutableTables.samplingNoise S r Ds)
      (S.radius r (snodes i)) Ds (sfinal i).shiftVector)
    (hpsm : ∀ i, QueryShift (smain i).program (smain i).enumeration
      (smain i).coefficient (S.radius r (snodes i)) (smain i).shiftVector)
    (hpsf : ∀ i, QueryShift (sfinal i).program (sfinal i).enumeration
      (sfinal i).coefficient (S.radius r (snodes i)) (sfinal i).shiftVector) :
    let sampling := SamplingExecutable.build S snodes r Ds smain sfinal layers
    let privateShift := SamplingExecutable.weights S snodes r Ds smain sfinal layers
      (-2*M.R/backwardEnd M.R)
    let data := SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w
      main final sampling layers privateShift
    QueryShift data.program data.enumeration data.coefficient r data.shiftVector := by
  let sampling := SamplingExecutable.build S snodes r Ds smain sfinal layers
  let privateShift := SamplingExecutable.weights S snodes r Ds smain sfinal layers
    (-2*M.R/backwardEnd M.R)
  let data := SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w
    main final sampling layers privateShift
  change QueryShift data.program data.enumeration data.coefficient r data.shiftVector
  apply queryShift_of_fullTranslation data r
  intro d G x P Δ tape
  let coeff := SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling
  let input : Inputs d (SourceMeanExecutable.size (a := a) main final sampling) := ⟨coeff,x,P⟩
  let input' : Inputs d (SourceMeanExecutable.size (a := a) main final sampling) := ⟨coeff,x+Δ,P⟩
  let inner := SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers
  let innerWeights := SourceMeanExecutable.incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift
  let baseTape : Tape d inner := tape.2.2
  let shifted := translate inner innerWeights r Δ baseTape
  let aPrivate := -1/r + ((M.R/backwardEnd M.R)/2)*((-2*M.R/backwardEnd M.R)/r)
  let slots : Fin sampling.size → Fin (SourceMeanExecutable.size (a := a) main final sampling) :=
    SourceMeanExecutable.prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot
  let child : Prog (SourceMeanExecutable.size (a := a) main final sampling) [.point,.point] .point :=
    sampling.program.embed slots (.there .here) .here
  have hchild (X Q : Point d) (stape : Tape d sampling.program) :
      run sampling.program G ⟨sampling.coefficient,X+Δ,Q⟩ Env.empty
        (translate sampling.program privateShift r Δ stape) =
      let result := run sampling.program G ⟨sampling.coefficient,X,Q⟩ Env.empty stape
      (⟨(show Point d from result.value) + aPrivate • Δ,result.trace⟩ : Result d .point) := by
    have ht := PrivateSamplingProgram.source_code_translation S snodes r Ds smain sfinal layers
      hpm hpf hr hpsm hpsf G X Q Δ (-2*M.R/backwardEnd M.R) stape
    change run sampling.program G ⟨sampling.coefficient,X+Δ,Q⟩ Env.empty
        (translate sampling.program privateShift r Δ stape) =
      let result := run sampling.program G ⟨sampling.coefficient,X,Q⟩ Env.empty stape
      (⟨(show Point d from result.value) + (-1/r+(S.τ/2)*((-2*M.R/backwardEnd M.R)/r)) • Δ,
        result.trace⟩ : Result d .point) at ht
    rw [hτ] at ht
    exact ht
  let first := run child G input (inputEnv x P) (baseTape.1 0)
  have hp : run child G input' (inputEnv (x+Δ) P) (shifted.1 0) =
      (⟨(show Point d from first.value) + aPrivate • Δ, first.trace⟩ : Result d .point) := by
    change run child G input' (inputEnv (x+Δ) P)
      ((translate inner innerWeights r Δ baseTape).1 0) = _
    rw [incoming_private]
    exact embedded_translation slots sampling.program (.there .here) .here privateShift sampling.coefficient
      r aPrivate G input input' (inputEnv x P) (inputEnv (x+Δ) P) Δ rfl
      (private_table M nodes anchors r σ Ds δ t w main final sampling) rfl rfl hchild (baseTape.1 0)
  let raw : Fin (m+1) → Point d := fun i => (baseTape.2.2.1 i).1
  let Z : Fin h → Point d := fun i => (baseTape.2.2.2.2.1 i).1
  have hraw : (fun i => (shifted.2.2.1 i).1) = raw := by
    funext i
    exact incoming_raw M nodes anchors seeds r σ Ds main final sampling layers privateShift Δ baseTape i
  have hZ : (fun i => (shifted.2.2.2.2.1 i).1) = Z := by
    funext i
    exact incoming_flow M nodes anchors seeds r σ Ds main final sampling layers privateShift Δ baseTape i
  have htail : shifted.2.2.2.2.2.2 =
      translate (SourceMeanExecutable.body (a := a) (h := h) M nodes main final sampling layers)
        (SourceMeanExecutable.bodyShift M nodes r σ Ds main final sampling layers) r Δ baseTape.2.2.2.2.2.2 :=
    incoming_tail M nodes anchors seeds r σ Ds main final sampling layers privateShift Δ baseTape
  let env : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]) := cache M nodes anchors seeds r σ Ds δ t w main final sampling x P first.value raw Z
  let env' : Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]) := cache M nodes anchors seeds r σ Ds δ t w main final sampling
    (x+Δ) P ((show Point d from first.value) + aPrivate • Δ) raw Z
  have hbdy := SourceMeanBodyShift.translation M nodes anchors r σ Ds δ t w main final sampling
    layers hr hm hsm G x P Δ env env'
    (fun i => cache_direct_translation M nodes anchors seeds r σ Ds δ t w main final sampling
      hr x P first.value Δ raw Z i)
    (by rw [cache_retained, cache_retained])
    (fun i => by rw [cache_designated, cache_designated]) baseTape.2.2.2.2.2.2
  have ht := run_incoming M nodes anchors seeds r σ Ds δ t w main final sampling layers G (x+Δ) P shifted
  have hb := run_incoming M nodes anchors seeds r σ Ds δ t w main final sampling layers G x P baseTape
  dsimp only at ht hb
  change run inner G input' (inputEnv (x+Δ) P) shifted = _ at ht
  change run inner G input (inputEnv x P) baseTape = _ at hb
  erw [hp] at ht
  simp only [hraw, hZ, htail] at ht
  change run inner G input' (inputEnv (x+Δ) P) shifted = run inner G input (inputEnv x P) baseTape
  rw [ht,hb]
  erw [hbdy]

end AcceleratedLogConcave.Oracle.SourceMeanQueryShift
