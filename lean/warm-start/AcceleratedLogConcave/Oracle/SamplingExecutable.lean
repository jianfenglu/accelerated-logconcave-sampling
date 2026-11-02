import AcceleratedLogConcave.Oracle.SourceExecutableTables
import AcceleratedLogConcave.Oracle.SourceExecutableShift
import AcceleratedLogConcave.Oracle.TerminalMean

/-! Actual sampling syntax, public data and bottom-up Gaussian shifts. The
recursive mean constructor supplies children at their prescribed lower precision. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SamplingExecutable
open Numerics.AffineGraph TapeLowering SourceExecutableTables
variable (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
  (main final : Fin n → ExecutableData) (layers : ℕ)

def raw (children : Fin n → ExecutableData) (i : Fin n) :
    Fin (tapeShape (children i).program).gaussianBlocks → ℝ :=
  LayerShift.rawShift (samplingNoise S r Ds) (S.radius r (e i)) r
    (1-S.mesh.location m (e i)*samplingEnd S.τ) (children i).shiftVector

/-- `reserveExtra=0` is the ordinary sampling shift. The enclosing mean
uses its explicit additional private reserve translation without changing code. -/
def weights (reserveExtra : ℝ) :
    GaussianSlot (PrivateSamplingProgram.code (samplingConfig main final layers)) → ℝ :=
  SourceExecutableShift.sampling (samplingConfig main final layers)
    (-(samplingEnd S.τ)) (raw S e r Ds main) (raw S e r Ds final) reserveExtra

def build : ExecutableData where
  size := samplingSize main final
  program := PrivateSamplingProgram.code (samplingConfig main final layers)
  coefficient := samplingTable S e r Ds main final
  shift := weights S e r Ds main final layers 0

/-- Every executed mean child is paid, including the fresh final children. -/
theorem queries_build : syntaxCount .gradient (build S e r Ds main final layers).program =
    layers * (∑ i, syntaxCount .gradient (main i).program) +
      ∑ i, syntaxCount .gradient (final i).program :=
  PrivateSamplingProgram.queries_code (samplingConfig main final layers)

end AcceleratedLogConcave.Oracle.SamplingExecutable
