import AcceleratedLogConcave.Oracle.RecursiveRootStabilityBounds
import AcceleratedLogConcave.Oracle.RecursiveReachableRows
import AcceleratedLogConcave.Oracle.RecursiveAdmissibleStability

/-! Deterministic uniform stability from the published certified-root schedule.
Admissibility is instantiated with actual occurrence paths. Root SizeBound and
the exact geometric schedule are explicit; no descendant or height conclusion
is assumed. Public-sampler initialization, accuracy and law are not asserted. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Numerics.AffineGraph RecursiveExecutable RecursiveSize FixedTapeStability Precision TapeLowering
open scoped BigOperators NNReal

variable {m n ns : ℕ}

/-- Existential actual-path predicate; no unused parameter family is included. -/
def Reachable (C : Source m n ns) (root p : State) : Prop :=
  ∃ depth cost, Path C root p depth cost

theorem reachable_root (C : Source m n ns) (root : State) : Reachable C root root :=
  ⟨0, 0, Path.refl root⟩

theorem Reachable.step {C : Source m n ns} {root p c : State}
    (hp : Reachable C root p) (o : Occurrence C.layers n ns m) (he : Edge C p o c) :
    Reachable C root c := by
  obtain ⟨depth, cost, hp⟩ := hp
  exact ⟨depth+1, cost+o.cost, hp.snoc o he⟩

/-- The psi inequality used by the operational mean theorem follows from the
two source identities; it is not an additional geometry hypothesis. -/
theorem Source.psi_eq_radius_fourth (C : Source m n ns) (hδ : 0 < C.δ)
    (hR : C.M.R = C.δ^C.t) (hpsi : C.M.psi = C.δ^(4*C.t)) :
    C.M.psi = C.M.R^4 := by
  rw [hpsi, hR, ← Real.rpow_mul_natCast hδ.le]
  congr 1
  norm_num
  ring

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

include hG hroot hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns
  hcost hres hpsi hhalf hback

/-- Sharper endpoint factor, with fuel equal to the endpoint's actual rank.
The root resolution cap pays the height condition, including root height zero. -/
theorem Path.certified_childStable_fuel {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) :
    ChildStable (E p.radius p.width p.precision).program
      (E p.radius p.width p.precision).coefficient G
      ((L : ℝ)*(1+20*C.δ^((1 : ℝ)/3))^(precisionRank C.t p.precision)) := by
  have hη := resolution_pays_height hm B hB (precisionRank C.t root.precision) hδ hδ1 hres
  have hpsi' := (C.psi_eq_radius_fourth hδ hR hpsi).le
  have hsmall (p : State) (hp : Reachable C root p) :
      (L : ℝ)*actualRowMass C.M p.radius p.width ≤ C.δ^((1 : ℝ)/3) ∧
      (L : ℝ)*p.radius^2 ≤ C.δ^((1 : ℝ)/3) := by
    obtain ⟨depth, cost, hp⟩ := hp
    have hs := hp.actual_rows_small (L : ℝ) B hroot hm L.coe_nonneg hr hσ hDs hδ hδ1
      ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback
    refine ⟨actualRowMass_small_of_rows C.M p.radius p.width L hη.1 hs.1, ?_⟩
    have hn : 0 ≤ (L : ℝ)*p.radius^2 := mul_nonneg L.coe_nonneg (sq_nonneg _)
    nlinarith [hs.2]
  have hrad (p : State) (hp : Reachable C root p) : 0 ≤ p.radius := by
    obtain ⟨depth, cost, hp⟩ := hp
    exact (hp.positive (by omega) hDs hδ hr hσ).1.le
  have hrank := hp.depth_rank_le ht htq
  exact childStable_admissible_fuel C anchors seeds ht htq scale G L hG (by omega) hpsi'
    (C.δ^((1 : ℝ)/3)) (precisionRank C.t root.precision) hη.1 hη.2.1 hη.2.2
    (Reachable C root)
    (fun _ o _ hp he => hp.step o he)
    (fun p hp _ => hrad p hp) (fun p hp _ => (hsmall p hp).1) (fun p hp _ => (hsmall p hp).2)
    (precisionRank C.t p.precision) p (by omega) ⟨depth, cost, hp⟩ le_rfl

/-- Every endpoint of an actual path from the certified root has the uniform
2L bound. No admissible-predicate or height premise remains in this interface. -/
theorem Path.certified_childStable {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) :
    ChildStable (E p.radius p.width p.precision).program
      (E p.radius p.width p.precision).coefficient G (2*(L : ℝ)) := by
  have hs := Path.certified_childStable_fuel C anchors seeds scale G L hG root B hroot
    hm hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback hp
  apply hs.mono
  have hη := resolution_pays_height hm B hB (precisionRank C.t root.precision) hδ hδ1 hres
  have hrank := hp.depth_rank_le ht htq
  have hF := (height_factor_mem (precisionRank C.t root.precision)
    (precisionRank C.t p.precision) hη.1 (by omega) hη.2.2).2
  nlinarith [L.coe_nonneg]

theorem certified_root_childStable :
    ChildStable (E root.radius root.width root.precision).program
      (E root.radius root.width root.precision).coefficient G (2*(L : ℝ)) :=
  Path.certified_childStable C anchors seeds scale G L hG root B hroot hm hr hσ hDs hδ hδ1
    ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback (Path.refl root)

/-- The published source wrapper uses the same literal private geometry. -/
theorem certified_source_childStable :
    ChildStable
      (RecursiveExecutable.mean C.M C.nodes anchors seeds C.Ds C.δ C.t C.w ht htq C.layers
        C.mesh C.snodes scale root.radius root.width root.precision).program
      (RecursiveExecutable.mean C.M C.nodes anchors seeds C.Ds C.δ C.t C.w ht htq C.layers
        C.mesh C.snodes scale root.radius root.width root.precision).coefficient G (2*(L : ℝ)) :=
  certified_root_childStable C anchors seeds scale G L hG root B hroot hm hr hσ hDs hδ hδ1
    ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback

/-- Stored output points on the same entering momentum and complete raw tape;
the actual state-dependent coefficient table is retained. -/
theorem Path.certified_sub_le {p : State} {depth cost : ℕ}
    (hp : Path C root p depth cost) (momentum x y : Point d)
    (tape : Tape d (E p.radius p.width p.precision).program) :
    ‖RetainedMeanFinalBatch.childPoint (run (E p.radius p.width p.precision).program G
        ⟨(E p.radius p.width p.precision).coefficient,x,momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run (E p.radius p.width p.precision).program G
        ⟨(E p.radius p.width p.precision).coefficient,y,momentum⟩ Env.empty tape)‖ ≤
      2*(L : ℝ)*‖x-y‖ :=
  childStable_tape _ _ G _
    (Path.certified_childStable C anchors seeds scale G L hG root B hroot hm hr hσ hDs hδ hδ1
      ht ht60 hw hwt hB hR hDsBound hn hns hcost hres hpsi hhalf hback hp) momentum x y tape

end CertifiedRoot
end AcceleratedLogConcave.Oracle.RecursiveCall
