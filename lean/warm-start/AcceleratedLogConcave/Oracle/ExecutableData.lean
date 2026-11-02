import AcceleratedLogConcave.Oracle.TapeLowering

/-! Data returned by the executable recursion. No correctness, law, shift,
accuracy, or work conclusion is assumed in this record. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle
open TapeLowering
structure ExecutableData where
  size : ℕ
  program : Program size .point
  coefficient : Fin size → ℝ
  shift : GaussianSlot program → ℝ
namespace ExecutableData
/-- Fixed complete enumeration of the actual structural Gaussian occurrences. -/
def enumeration (p : ExecutableData) :
    GaussianSlot p.program ≃ Fin (tapeShape p.program).gaussianBlocks :=
  gaussianSlotEquiv p.program

def shiftVector (p : ExecutableData) : Fin (tapeShape p.program).gaussianBlocks → ℝ :=
  fun i => p.shift (p.enumeration.symm i)
end ExecutableData
end AcceleratedLogConcave.Oracle
