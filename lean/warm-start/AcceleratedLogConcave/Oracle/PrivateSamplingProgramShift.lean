import AcceleratedLogConcave.Oracle.PrivateSamplingBodyShift
import AcceleratedLogConcave.Oracle.SourceExecutableTables

noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateSamplingProgram
open AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram RecursiveMeanContinuation
open ChildAbsorption CovarianceSetup LayerShift ExecutableShiftWeights SourceExecutableShift
open scoped BigOperators

variable {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
  {pf : ∀ i, Program (cf i) .point}

def nodeDisplacement (cfg : Config n C c cf p pf) (coeff : Fin C → ℝ)
    (position r : ℝ) (i : Fin n) : ℝ :=
  1 + coeff (cfg.directWeight i) * (position/r)

def outputDisplacement (cfg : Config n C c cf p pf) (coeff : Fin C → ℝ)
    (position reserveShift r : ℝ) : ℝ :=
  coeff cfg.invEnd * (position/r) + coeff cfg.reserve * (reserveShift/r)

set_option backward.isDefEq.respectTransparency false in
/-- Full executed sampling-program translation. Every child, residual draw,
reserve draw, and complete oracle transcript is retained. -/
theorem code_translation (cfg : Config n C c cf p pf)
    (rho r Ds : ℝ) (radius : Fin n → ℝ)
    (vm : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (vf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (cm : ∀ i, Fin (c i) → ℝ) (cfinal : ∀ i, Fin (cf i) → ℝ)
    (hm : ∀ i, Admissible rho (radius i) Ds (vm i))
    (hf : ∀ i, Admissible rho (radius i) Ds (vf i)) (hr : 0 < r)
    (hsm : ∀ i, QueryShift (p i) (cfg.mainEquiv i) (cm i) (radius i) (vm i))
    (hsf : ∀ i, QueryShift (pf i) (cfg.finalEquiv i) (cfinal i) (radius i) (vf i))
    (G : Point d → Point d) (coeff : Fin C → ℝ) (x P Δ : Point d)
    (position reserveShift : ℝ)
    (htm : ∀ i, coeff ∘ (cfg.mainSlots ∘ childSlot c p i) =
      matrixTable (childRoot rho (radius i) (vm i)) (cm i))
    (htf : ∀ i, coeff ∘ cfg.finalSlots i =
      matrixTable (childRoot rho (radius i) (vf i)) (cfinal i))
    (tape : Tape d (code cfg)) :
    run (code cfg) G ⟨coeff,x+Δ,P⟩ Env.empty
      (translate (code cfg)
        (sampling cfg position
          (fun i => rawShift rho (radius i) r (nodeDisplacement cfg coeff position r i) (vm i))
          (fun i => rawShift rho (radius i) r (nodeDisplacement cfg coeff position r i) (vf i))
          reserveShift) r Δ tape) =
    displaced (run (code cfg) G ⟨coeff,x,P⟩ Env.empty tape)
      (outputDisplacement cfg coeff position reserveShift r) Δ := by
  let input : Inputs d C := ⟨coeff,x,P⟩
  let input' : Inputs d C := ⟨coeff,x+Δ,P⟩
  let Y : Point d := tape.2.1
  let Y' := Y + (position/r) • Δ
  let mainRaw := fun i => rawShift rho (radius i) r
    (nodeDisplacement cfg coeff position r i) (vm i)
  let finalRaw := fun i => rawShift rho (radius i) r
    (nodeDisplacement cfg coeff position r i) (vf i)
  let shifted := translate (code cfg) (sampling cfg position mainRaw finalRaw reserveShift) r Δ tape
  have hd (i : Fin n) :
      storedPoint (setupEnv cfg input' Y') (batchRef i) =
      storedPoint (setupEnv cfg input Y) (batchRef i) +
        nodeDisplacement cfg coeff position r i • Δ := by
    rw [setupEnv_direct,setupEnv_direct]
    dsimp only [input,input',Y',nodeDisplacement]
    simp only [smul_add,smul_smul,add_smul,one_smul]
    abel
  have ho : storedPoint (setupEnv cfg input' Y') (RefMap.shiftMany n .here) =
      storedPoint (setupEnv cfg input Y) (RefMap.shiftMany n .here) +
        (coeff cfg.invEnd * (position/r)) • Δ := by
    rw [setupEnv_output,setupEnv_output]
    dsimp only [input,input',Y']
    simp only [smul_add,smul_smul]
  have ht := run_code_setup cfg G input' shifted
  have hb := run_code_setup cfg G input tape
  dsimp only at ht hb
  have hbody := body_translation cfg (RefMap.shiftMany n .here) rho r Ds radius
    (nodeDisplacement cfg coeff position r) vm vf cm cfinal hm hf hr hsm hsf G input input'
    rfl Δ (coeff cfg.invEnd * (position/r)) reserveShift htm htf batchRef
    (setupEnv cfg input Y) (setupEnv cfg input' Y') hd ho tape.2.2.2.2.2
  change run (code cfg) G input' Env.empty shifted = _
  rw [ht,hb]
  change (⟨(run (body cfg batchRef (RefMap.shiftMany n .here)) G input'
      (setupEnv cfg input' Y')
      (translate (body cfg batchRef (RefMap.shiftMany n .here))
        (samplingBody cfg batchRef (RefMap.shiftMany n .here) mainRaw finalRaw reserveShift)
        r Δ tape.2.2.2.2.2)).value,
    Event.gaussian cfg.positionOrigin :: (run (body cfg batchRef (RefMap.shiftMany n .here))
      G input' (setupEnv cfg input' Y')
      (translate (body cfg batchRef (RefMap.shiftMany n .here))
        (samplingBody cfg batchRef (RefMap.shiftMany n .here) mainRaw finalRaw reserveShift)
        r Δ tape.2.2.2.2.2)).trace⟩ : Result d .point) = _
  rw [hbody]
  rfl

open Numerics.AffineGraph SourceExecutableTables

set_option backward.isDefEq.respectTransparency false in
theorem source_nodeDisplacement (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (layers : ℕ) (hr : 0 < r)
    (i : Fin n) :
    nodeDisplacement (samplingConfig main final layers)
      (samplingTable S e r Ds main final) (-(samplingEnd S.τ)) r i =
      1 - S.mesh.location m (e i) * samplingEnd S.τ := by
  simp only [nodeDisplacement,samplingConfig,samplingTable_scalar,samplingScalarTable,
    Fin.append_left]
  field_simp [hr.ne']
  ring

set_option backward.isDefEq.respectTransparency false in
theorem source_outputDisplacement (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (layers : ℕ) (reserveShift : ℝ)
    (hr : 0 < r) :
    outputDisplacement (samplingConfig main final layers)
      (samplingTable S e r Ds main final) (-(samplingEnd S.τ)) reserveShift r =
      -1/r + (S.τ/2)*(reserveShift/r) := by
  have he : samplingEnd S.τ ≠ 0 := S.samplingEnd_pos.ne'
  simp only [outputDisplacement,samplingConfig,samplingTable_scalar,samplingScalarTable,
    Fin.append_right]
  norm_num
  field_simp [he,hr.ne']

set_option backward.isDefEq.respectTransparency false in
/-- The literal source sampling block, with no coefficient-routing hypotheses.
Only the inductively available smaller mean identities and covariance domains
are premises. The reserve correction is explicit and changes no query. -/
theorem source_code_translation (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (layers : ℕ)
    (hm : ∀ i, Admissible (samplingNoise S r Ds) (S.radius r (e i)) Ds
      (main i).shiftVector)
    (hf : ∀ i, Admissible (samplingNoise S r Ds) (S.radius r (e i)) Ds
      (final i).shiftVector) (hr : 0 < r)
    (hsm : ∀ i, QueryShift (main i).program (main i).enumeration (main i).coefficient
      (S.radius r (e i)) (main i).shiftVector)
    (hsf : ∀ i, QueryShift (final i).program (final i).enumeration (final i).coefficient
      (S.radius r (e i)) (final i).shiftVector)
    (G : Point d → Point d) (x P Δ : Point d) (reserveShift : ℝ)
    (tape : Tape d (code (samplingConfig main final layers))) :
    let cfg := samplingConfig main final layers
    let coeff := samplingTable S e r Ds main final
    let k := fun i => 1 - S.mesh.location m (e i) * samplingEnd S.τ
    run (code cfg) G ⟨coeff,x+Δ,P⟩ Env.empty
      (translate (code cfg)
        (sampling cfg (-(samplingEnd S.τ))
          (fun i => rawShift (samplingNoise S r Ds) (S.radius r (e i)) r (k i)
            (main i).shiftVector)
          (fun i => rawShift (samplingNoise S r Ds) (S.radius r (e i)) r (k i)
            (final i).shiftVector) reserveShift) r Δ tape) =
      displaced (run (code cfg) G ⟨coeff,x,P⟩ Env.empty tape)
        (-1/r + (S.τ/2)*(reserveShift/r)) Δ := by
  have htm (i : Fin n) : samplingTable S e r Ds main final ∘
      ((samplingConfig main final layers).mainSlots ∘
        childSlot (fun i => (main i).size) (fun i => (main i).program) i) =
      matrixTable (childRoot (samplingNoise S r Ds) (S.radius r (e i))
        (main i).shiftVector) (main i).coefficient := by
    funext j
    change samplingTable S e r Ds main final
      (mainSlot main final (childSlot (fun i => (main i).size)
        (fun i => (main i).program) i j)) = _
    rw [samplingTable_main]
    unfold samplingMainTable RecursiveMeanPublicTable.sourceLayerTable
    exact layerTable_child (fun i => (main i).size) (fun i => (main i).program)
      _ _ _ (fun i => (main i).coefficient) i j
  have htf (i : Fin n) : samplingTable S e r Ds main final ∘
      (samplingConfig main final layers).finalSlots i =
      matrixTable (childRoot (samplingNoise S r Ds) (S.radius r (e i))
        (final i).shiftVector) (final i).coefficient := by
    funext j
    exact samplingTable_final S e r Ds main final i j
  have ht := code_translation (samplingConfig main final layers) (samplingNoise S r Ds)
    r Ds (fun i => S.radius r (e i)) (fun i => (main i).shiftVector)
    (fun i => (final i).shiftVector) (fun i => (main i).coefficient)
    (fun i => (final i).coefficient) hm hf hr hsm hsf G (samplingTable S e r Ds main final)
    x P Δ (-(samplingEnd S.τ)) reserveShift htm htf tape
  simpa only [source_nodeDisplacement S e r Ds main final layers hr,
    source_outputDisplacement S e r Ds main final layers reserveShift hr] using ht

end AcceleratedLogConcave.Oracle.PrivateSamplingProgram
