import AcceleratedLogConcave.Oracle.RecursiveCertifiedSamplingStability
import AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability
import AcceleratedLogConcave.Oracle.PrivateAnchorCoefficient
import AcceleratedLogConcave.Oracle.SourceMeanPrivateReplacementRms

/-! Private-anchor propagation for the literal children of a reachable source
mean call. Child stability is discharged by actual occurrence paths from the
certified root. The zero-layer case uses final occurrences only. No private
accuracy, probability law, reference coupling, or nonterminal D2 is asserted. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Numerics.AffineGraph RecursiveExecutable RecursiveSize FixedTapeStability Precision TapeLowering
open SourceMeanPrivateAnchorStability
open RetainedMeanFinalBatch
open scoped BigOperators NNReal

variable {m n ns : ℕ}

/-- The prescribed main children, at their actual width and quarter precision drop. -/
def Source.meanMainChildren {a h : ℕ} (C : Source m n ns)
    (anchors : Fin a ≃ C.M.Anchor) (seeds : Fin h ≃ Fin m × C.M.Kernel)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (scale : ℝ) (p : State) (i : Fin n) : ExecutableData :=
  meanCore C.M C.nodes anchors seeds C.S C.snodes C.Ds C.δ C.t C.w C.layers ht htq scale
    (C.M.radius p.radius (C.nodes i))
    (RecursiveMeanPublicTable.mainWidth n p.radius C.M.R C.Ds
      (SourceMeanExecutable.rowBound (m := m) p.radius p.width C.δ C.t C.w))
    (p.precision-1/4)

/-- The prescribed paid final children, including their distinct final width. -/
def Source.meanFinalChildren {a h : ℕ} (C : Source m n ns)
    (anchors : Fin a ≃ C.M.Anchor) (seeds : Fin h ≃ Fin m × C.M.Kernel)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (scale : ℝ) (p : State) (_ : Fin m) : ExecutableData :=
  meanCore C.M C.nodes anchors seeds C.S C.snodes C.Ds C.δ C.t C.w C.layers ht htq scale
    (p.radius*C.M.R) (RecursiveMeanPublicTable.finalWidth C.M.R p.width) (p.precision-C.t)

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
local notation "main" => C.meanMainChildren anchors seeds ht htq scale
local notation "final" => C.meanFinalChildren anchors seeds ht htq scale
local notation "sampling" => C.privateSampler anchors seeds ht htq scale

include hG hroot hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns
  hcost hres hpsi hhalf hback

/-- Every paid final is an actual child, including when there are zero layers. -/
theorem Path.certified_activeFinal_childStable {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision) (i : Fin m) :
    ChildStable (final p i).program (final p i).coefficient G (2*(L : ℝ)) := by
  exact Path.certified_childStable C anchors seeds scale G L hG root B hroot hm hr hσ
    hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
    (hp.snoc (Occurrence.activeFinal i) ⟨hq,rfl⟩)

/-- A positive layer count supplies a genuine occurrence for each main child. -/
theorem Path.certified_meanMain_childStable {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision)
    (hN : 0 < C.layers) (i : Fin n) :
    ChildStable (main p i).program (main p i).coefficient G (2*(L : ℝ)) := by
  exact Path.certified_childStable C anchors seeds scale G L hG root B hroot hm hr hσ
    hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
    (hp.snoc (Occurrence.meanMain ⟨0,hN⟩ i) ⟨hq,rfl⟩)

/-- Propagation of an arbitrary private-anchor replacement through the same
complete body tape, with the prescribed actual recursive child programs. -/
theorem Path.certified_privateAnchor_sub_le {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision)
    (x P U V : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (τ : Tape d (SourceMeanExecutable.body (a := a) (h := h) C.M C.nodes
      (main p) (final p) (sampling p) C.layers)) :
    ‖output C.M C.nodes anchors seeds p.radius p.width C.Ds C.δ C.t C.w
        (main p) (final p) (sampling p) C.layers G x P U raw Z τ -
      output C.M C.nodes anchors seeds p.radius p.width C.Ds C.δ C.t C.w
        (main p) (final p) (sampling p) C.layers G x P V raw Z τ‖ ≤
      coefficient C.M p.radius C.layers (2*(L : ℝ))
        (actualRowMass C.M p.radius p.width) * ‖U-V‖ := by
  have hpr : 0 ≤ p.radius := (hp.positive (by omega) hDs hδ hr hσ).1.le
  have hpsi' := (C.psi_eq_radius_fourth hδ hR hpsi).le
  have hf (i : Fin m) : ChildStable (final p i).program (final p i).coefficient G (2*(L : ℝ)) :=
    Path.certified_activeFinal_childStable C anchors seeds scale G L hG root B hroot hm hr hσ
      hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback hp hq i
  by_cases hz : C.layers = 0
  · generalize hN : C.layers = N at τ ⊢
    have hN0 : N = 0 := hN.symm.trans hz
    clear hN
    subst N
    simpa only [coefficient,Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,zero_add,mul_one] using
      output_zero_sub_le C.M C.nodes anchors seeds p.radius p.width C.Ds C.δ C.t C.w
        (main p) (final p) (sampling p) G (2*(L : ℝ)) (by omega) hpr (by positivity)
        hpsi' hf x P U V raw Z τ
  · have hmain (i : Fin n) : ChildStable (main p i).program (main p i).coefficient G (2*(L : ℝ)) :=
      Path.certified_meanMain_childStable C anchors seeds scale G L hG root B hroot hm hr hσ
        hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
        hp hq (Nat.pos_of_ne_zero hz) i
    exact output_sub_le C.M C.nodes anchors seeds p.radius p.width C.Ds C.δ C.t C.w
      (main p) (final p) (sampling p) C.layers G (2*(L : ℝ))
      (actualRowMass C.M p.radius p.width) (by omega) hpr (by positivity)
      (NNReal.coe_nonneg _) hpsi' hmain hf (row_mass_le_actualRowMass C.M p.radius p.width)
      x P U V raw Z τ

omit hG in
/-- The original root schedule pays the half-contraction cap at every reachable
state; there is no division by the oracle constant. -/
theorem Path.certified_privateAnchor_contraction {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) :
    (2*(L : ℝ))*actualRowMass C.M p.radius p.width ≤ 1/2 := by
  have hη := resolution_pays_height hm B hB (precisionRank C.t root.precision) hδ hδ1 hres
  have hs := hp.actual_rows_small (L : ℝ) B hroot hm L.coe_nonneg hr hσ hDs hδ hδ1
    ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
  have hA := actualRowMass_small_of_rows C.M p.radius p.width L hη.1 hs.1
  nlinarith [hη.2.1]

omit hG in
/-- A radius-only private-anchor coefficient derived from the same certified
root caps, including the zero-curvature endpoint. -/
theorem Path.certified_privateAnchor_coefficient_le {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) :
    coefficient C.M p.radius C.layers (2*(L : ℝ))
      (actualRowMass C.M p.radius p.width) ≤ 4*(L : ℝ)*p.radius := by
  have hpr := (hp.positive (by omega) hDs hδ hr hσ).1.le
  have hA := Path.certified_privateAnchor_contraction C L root B hroot hm hr hσ hDs hδ hδ1
    ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback hp
  calc
    _ ≤ 2*(2*(L : ℝ))*p.radius := coefficient_le_twice_radius C.M p.radius C.layers
      (2*(L : ℝ)) (actualRowMass C.M p.radius p.width)
      hpr (by positivity) (NNReal.coe_nonneg _) hA
    _ = _ := by ring

/-- The fully discharged source-child propagation bound. The shared tape,
original P, assembly and flow coordinates remain identical on both sides. -/
theorem Path.certified_privateAnchor_sub_le_four {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision)
    (x P U V : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (τ : Tape d (SourceMeanExecutable.body (a := a) (h := h) C.M C.nodes
      (main p) (final p) (sampling p) C.layers)) :
    ‖output C.M C.nodes anchors seeds p.radius p.width C.Ds C.δ C.t C.w
        (main p) (final p) (sampling p) C.layers G x P U raw Z τ -
      output C.M C.nodes anchors seeds p.radius p.width C.Ds C.δ C.t C.w
        (main p) (final p) (sampling p) C.layers G x P V raw Z τ‖ ≤
      (4*(L : ℝ)*p.radius) * ‖U-V‖ := by
  have hb := Path.certified_privateAnchor_sub_le C anchors seeds scale G L hG root B hroot
    hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
    hp hq x P U V raw Z τ
  have hc := Path.certified_privateAnchor_coefficient_le C L root B hroot hm hr hσ hDs hδ hδ1
    ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback hp
  exact hb.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

/-- Executed full-build interface: the actual private result is compared with
an arbitrary replacement in the same cache and complete downstream tape.
The sampler and its shift remain literal; no private accuracy is supplied. -/
theorem Path.certified_build_privateAnchor_sub_le {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (hq : 1/2 < p.precision)
    (privateShift : GaussianSlot (sampling p).program → ℝ) (x P V : Point d)
    (τ : Tape d (SourceMeanExecutable.build C.M C.nodes anchors seeds p.radius p.width
      C.Ds C.δ C.t C.w (main p) (final p) (sampling p) C.layers privateShift).program) :
    ‖childPoint (run (SourceMeanExecutable.build C.M C.nodes anchors seeds p.radius p.width
        C.Ds C.δ C.t C.w (main p) (final p) (sampling p) C.layers privateShift).program
        G ⟨SourceMeanExecutable.table C.M C.nodes anchors p.radius p.width C.Ds C.δ C.t C.w
          (main p) (final p) (sampling p),x,P⟩ Env.empty τ) -
      childPoint (run (SourceMeanExecutable.body (a := a) (h := h) C.M C.nodes
        (main p) (final p) (sampling p) C.layers)
        G ⟨SourceMeanExecutable.table C.M C.nodes anchors p.radius p.width C.Ds C.δ C.t C.w
          (main p) (final p) (sampling p),x,P⟩
        (SourceMeanPrivateReplacementRms.replacementEnv C.M C.nodes anchors seeds
          p.radius p.width C.Ds C.δ C.t C.w (main p) (final p) (sampling p) C.layers
          privateShift x P V τ)
        (SourceMeanBuildRms.actualTape C.M C.nodes anchors seeds p.radius p.width
          C.Ds C.δ C.t C.w (main p) (final p) (sampling p) C.layers privateShift τ))‖ ≤
      (4*(L : ℝ)*p.radius) *
        ‖SourceMeanBuildRms.privateResult C.M C.nodes anchors seeds p.radius p.width
          C.Ds C.δ C.t C.w (main p) (final p) (sampling p) C.layers privateShift G x P τ - V‖ := by
  rw [build_eq_output]
  exact Path.certified_privateAnchor_sub_le_four C anchors seeds scale G L hG root B hroot
    hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
    hp hq x P
    (SourceMeanBuildRms.privateResult C.M C.nodes anchors seeds p.radius p.width
      C.Ds C.δ C.t C.w (main p) (final p) (sampling p) C.layers privateShift G x P τ) V
    (fun i => (τ.2.2.2.2.1 i).1) (fun i => (τ.2.2.2.2.2.2.1 i).1)
    (SourceMeanBuildRms.actualTape C.M C.nodes anchors seeds p.radius p.width
      C.Ds C.δ C.t C.w (main p) (final p) (sampling p) C.layers privateShift τ)

end CertifiedRoot
end AcceleratedLogConcave.Oracle.RecursiveCall
