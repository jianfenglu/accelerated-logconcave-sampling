import AcceleratedLogConcave.Oracle.RecursiveCertifiedRootStability
import AcceleratedLogConcave.Oracle.SamplingZeroLayerStability

/-! Actual private sampling stability at reachable nonterminal calls. The
mean children are the existing certified-root meanCore programs. The ordinary
sampler shift retains reserveExtra = 0; it is not the enclosing mean shift.
No public initialization, probability law, accuracy, or new recursion is added. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Numerics.AffineGraph RecursiveExecutable RecursiveSize FixedTapeStability Precision TapeLowering
open scoped BigOperators NNReal
variable {m n ns : ℕ}

/-- Literal private sampling block with both mean families at precision q-1/4.
The main width and final width remain the actual, distinct source widths. -/
def Source.privateSampler {a h : ℕ} (C : Source m n ns)
    (anchors : Fin a ≃ C.M.Anchor) (seeds : Fin h ≃ Fin m × C.M.Kernel)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (scale : ℝ) (p : State) : ExecutableData :=
  let E := meanCore C.M C.nodes anchors seeds C.S C.snodes
    C.Ds C.δ C.t C.w C.layers ht htq scale
  SamplingExecutable.build C.S C.snodes p.radius C.Ds
    (fun i => E (C.S.radius p.radius (C.snodes i))
      (RecursiveMeanPublicTable.mainWidth ns p.radius C.S.R C.Ds (p.radius^2))
      (p.precision-1/4))
    (fun i => E (C.S.radius p.radius (C.snodes i))
      (SourceExecutableTables.samplingFinalWidth C.S p.radius) (p.precision-1/4)) C.layers

section CertifiedRoot
variable {d a h : ℕ} (C : Source m n ns)
    (anchors : Fin a ≃ C.M.Anchor) (seeds : Fin h ≃ Fin m × C.M.Kernel)
    (scale : ℝ) (G : Point d → Point d) (L : ℝ≥0)
    (hG : LipschitzWith L (fun x => scale • G (scale • x)))
    (root : State) (B : ℝ)
    (hroot : SizeBound L C.δ 1 1 root.radius root.width)
    (hm : 2 ≤ m) (hr : 0 < root.radius) (hσ : 0 < root.width)
    (hDs : 0 < C.Ds) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)
    (ht : 0 < C.t) (ht60 : C.t ≤ 1/60) (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
    (hR : C.M.R = C.δ^C.t) (hDsBound : C.Ds ≤ C.δ^(-C.t))
    (hn : Real.sqrt n ≤ B*C.δ^(-C.w)) (hns : Real.sqrt ns ≤ B*C.δ^(-C.w))
    (hcost : 10*C.t*(precisionRank (1/4) root.precision : ℝ) ≤ 1/2)
    (hres : C.δ ≤ (520*(m : ℝ)^5*(stepFactor m B)^(precisionRank C.t root.precision))^(-12 : ℝ))
    (hpsi : C.M.psi = C.δ^(4*C.t)) (hhalf : C.δ^C.w ≤ 1/2)
    (hback : C.M.backward = actualKernelInterval C.M.R (C.δ^C.w)
      C.M.R_pos C.M.R_le_half (Real.rpow_pos_of_pos hδ C.w))

local notation "htq" => ht60.trans (by norm_num : (1 : ℝ)/60 ≤ 1/4)
local notation "E" => meanCore C.M C.nodes anchors seeds C.S C.snodes
  C.Ds C.δ C.t C.w C.layers ht htq scale
local notation "Samp" => C.privateSampler anchors seeds ht htq scale

include hG hroot hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns
  hcost hres hpsi hhalf hback

/-- Finite sampler bound, deriving all used child bounds from genuine paths.
At zero layers only final occurrences are used; no unused main IH is asserted. -/
theorem Path.certified_privateSampler_growth {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision) :
    ChildStable (Samp p).program (Samp p).coefficient G
      (samplingGrowth C.layers (2*(L : ℝ)) p.radius) := by
  let smain : Fin ns → ExecutableData := fun i => E (C.S.radius p.radius (C.snodes i))
    (RecursiveMeanPublicTable.mainWidth ns p.radius C.S.R C.Ds (p.radius^2)) (p.precision-1/4)
  let sfinal : Fin ns → ExecutableData := fun i => E (C.S.radius p.radius (C.snodes i))
    (SourceExecutableTables.samplingFinalWidth C.S p.radius) (p.precision-1/4)
  have hpr := (hp.positive (by omega) hDs hδ hr hσ).1.le
  have hsf (i : Fin ns) : ChildStable (sfinal i).program (sfinal i).coefficient G (2*(L : ℝ)) := by
    exact Path.certified_childStable C anchors seeds scale G L hG root B hroot hm hr hσ
      hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
      (hp.snoc (Occurrence.samplingFinal i) ⟨hq, rfl⟩)
  change ChildStable (SamplingExecutable.build C.S C.snodes p.radius C.Ds smain sfinal C.layers).program
    (SamplingExecutable.build C.S C.snodes p.radius C.Ds smain sfinal C.layers).coefficient G _
  by_cases hz : C.layers = 0
  · have hb := FixedTapeSampling.build_zero_childStable C.S C.snodes p.radius C.Ds smain sfinal
      G (2*(L : ℝ)) (by omega) hpr (by positivity) hsf
    rw [hz, samplingGrowth_zero_layers]
    exact hb
  · have hsm (i : Fin ns) : ChildStable (smain i).program (smain i).coefficient G (2*(L : ℝ)) := by
      exact Path.certified_childStable C anchors seeds scale G L hG root B hroot hm hr hσ
        hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
        (hp.snoc (Occurrence.samplingMain ⟨0, Nat.pos_of_ne_zero hz⟩ i) ⟨hq, rfl⟩)
    exact FixedTapeSampling.build_childStable C.S C.snodes p.radius C.Ds smain sfinal C.layers
      G (2*(L : ℝ)) (by omega) hpr (by positivity) hsm hsf

/-- The existing root cap pays the sampler absorption at F=2. No supplied
child, size, eta, layer positivity, or strengthened threshold premise remains. -/
theorem Path.certified_privateSampler_childStable {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision) :
    ChildStable (Samp p).program (Samp p).coefficient G (5*p.radius*(L : ℝ)) := by
  have hb := Path.certified_privateSampler_growth C anchors seeds scale G L hG root B hroot
    hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback hp hq
  apply hb.mono
  have hη := resolution_pays_height hm B hB (precisionRank C.t root.precision) hδ hδ1 hres
  have hs := hp.actual_rows_small (L : ℝ) B hroot hm L.coe_nonneg hr hσ hDs hδ hδ1
    ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
  have hsize : (L : ℝ)*p.radius^2 ≤ C.δ^((1 : ℝ)/3) := by
    nlinarith [hs.2, mul_nonneg L.coe_nonneg (sq_nonneg p.radius)]
  exact samplingGrowth_le_five C.layers (by norm_num : (0 : ℝ) ≤ 2) le_rfl L.coe_nonneg
    (hp.positive (by omega) hDs hδ hr hσ).1.le hη.1 hη.2.1 hsize

/-- Root specialization requires the root to select its nonterminal branch. -/
theorem certified_root_privateSampler_childStable (hq : 1/2 < root.precision) :
    ChildStable (Samp root).program (Samp root).coefficient G (5*root.radius*(L : ℝ)) :=
  Path.certified_privateSampler_childStable C anchors seeds scale G L hG root B hroot
    hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
    (Path.refl root) hq

/-- Literal stored output points with the same entering momentum and full raw
sampler tape. This is no claim of equality of traces or complete Results. -/
theorem Path.certified_privateSampler_sub_le {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision) (momentum x y : Point d)
    (tape : Tape d (Samp p).program) :
    ‖RetainedMeanFinalBatch.childPoint (run (Samp p).program G
        ⟨(Samp p).coefficient,x,momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run (Samp p).program G
        ⟨(Samp p).coefficient,y,momentum⟩ Env.empty tape)‖ ≤
      (5*p.radius*(L : ℝ))*‖x-y‖ :=
  childStable_tape _ _ G _
    (Path.certified_privateSampler_childStable C anchors seeds scale G L hG root B hroot
      hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback hp hq)
    momentum x y tape

end CertifiedRoot
end AcceleratedLogConcave.Oracle.RecursiveCall
