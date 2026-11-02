import AcceleratedLogConcave.Oracle.RecursiveExecutableDomain
import AcceleratedLogConcave.Oracle.SourceMeanQueryShift
import AcceleratedLogConcave.Oracle.SourceExecutableMass
import AcceleratedLogConcave.Oracle.SamplingExecutableMass

/-! Simultaneous query-shift and actual shift-mass induction for the constructed
precision program. Its explicit finite scalar budget is still to be derived from
the manuscript's prescribed public schedule; no child outcome is assumed. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph TapeLowering Precision ChildAbsorption CovarianceSetup
open RecursiveExecutableDomain
open scoped BigOperators

def shiftBase (layers n ns : ℕ) : ℝ := 5+36*(layers*n+(layers+1)*ns : ℕ)

theorem shiftBase_ge_one (layers n ns : ℕ) : 1 ≤ shiftBase layers n ns := by
  have hn : (0:ℝ) ≤ (layers*n+(layers+1)*ns : ℕ) := Nat.cast_nonneg _
  unfold shiftBase
  linarith

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
set_option backward.isDefEq.respectTransparency false in
theorem meanCore_queryShift_and_mass
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)
    (K scale : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
    (hτ : S.τ = M.R/backwardEnd M.R)
    (hbudget : shiftBase layers n ns ^ precisionRank (1/4) K ≤ Ds^2)
    (r σ q : ℝ) (hr : 0 < r) (hqK : q ≤ K) :
    let data := meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q
    QueryShift data.program data.enumeration data.coefficient r data.shiftVector ∧
      shiftSq data.shiftVector ≤ shiftBase layers n ns ^ precisionRank (1/4) q := by
  let C := shiftBase layers n ns
  have hC : 1 ≤ C := shiftBase_ge_one layers n ns
  have hstep : (0:ℝ) < 1/4 := by norm_num
  suffices hall : ∀ rank : ℕ, ∀ q : ℝ, precisionRank (1/4) q = rank → q ≤ K → ∀ r σ : ℝ,
      0 < r →
      let data := meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q
      QueryShift data.program data.enumeration data.coefficient r data.shiftVector ∧
        shiftSq data.shiftVector ≤ C^rank by
    exact hall _ q rfl hqK r σ hr
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
    intro q heq hqK r σ hr
    by_cases hq : q ≤ 1/2
    · rw [mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq layers scale r σ q hq]
      constructor
      · exact terminal_queryShift scale r σ hr
      · change shiftSq (fun _ : Fin 1 => (-1:ℝ)) ≤ C^rank
        rw [TerminalMeanShift.shiftSq_terminal]
        exact one_le_pow₀ hC
    · have hq' : 1/2 < q := lt_of_not_ge hq
      have hd : precisionRank (1/4) (q-1/4)+1 ≤ rank := by
        rw [← heq]
        exact precisionRank_drop hstep hq' le_rfl
      have hpos : 0 < rank := by omega
      have iq (r' σ' : ℝ) (hr' : 0 < r') :=
        ih _ (by omega) (q-1/4) rfl (by linarith : q-1/4 ≤ K) r' σ' hr'
      have childMass (r' σ' : ℝ) (hr' : 0 < r') :
          shiftSq (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
            scale r' σ' (q-1/4)).shiftVector ≤ C^(rank-1) :=
        (iq r' σ' hr').2.trans (pow_le_pow_right₀ hC (by omega))
      have childBudget (r' σ' : ℝ) (hr' : 0 < r') :
          shiftSq (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
            scale r' σ' (q-1/4)).shiftVector ≤ Ds^2 := by
        exact (iq r' σ' hr').2.trans ((pow_le_pow_right₀ hC
          (precisionRank_mono hstep (by linarith : q-1/4 ≤ K))).trans hbudget)
      let main : Fin n → ExecutableData := fun i => meanCore M nodes anchors seeds S snodes
        Ds δ t w layers ht htq scale (M.radius r (nodes i))
          (RecursiveMeanPublicTable.mainWidth n r M.R Ds (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4)
      let final : Fin m → ExecutableData := fun _ => meanCore M nodes anchors seeds S snodes
        Ds δ t w layers ht htq scale (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)
      let smain : Fin ns → ExecutableData := fun i => meanCore M nodes anchors seeds S snodes
        Ds δ t w layers ht htq scale (S.radius r (snodes i))
          (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4)
      let sfinal : Fin ns → ExecutableData := fun i => meanCore M nodes anchors seeds S snodes
        Ds δ t w layers ht htq scale (S.radius r (snodes i)) (SourceExecutableTables.samplingFinalWidth S r) (q-1/4)
      let sampling := SamplingExecutable.build S snodes r Ds smain sfinal layers
      let privateShift := SamplingExecutable.weights S snodes r Ds smain sfinal layers (-2*M.R/backwardEnd M.R)
      have hm (i) : Admissible (RecursiveMeanPublicTable.centerNoise r M.R Ds)
          (M.radius r (nodes i)) Ds (main i).shiftVector :=
        mean_admissible M r Ds hr hDs (nodes i) _ (childBudget _ _ (M.radius_pos r hr (nodes i)))
      have hpm (i) : Admissible (SourceExecutableTables.samplingNoise S r Ds)
          (S.radius r (snodes i)) Ds (smain i).shiftVector :=
        sampling_admissible S r Ds hr hDs (snodes i) _ (childBudget _ _ (S.radius_pos r hr (snodes i)))
      have hpf (i) : Admissible (SourceExecutableTables.samplingNoise S r Ds)
          (S.radius r (snodes i)) Ds (sfinal i).shiftVector :=
        sampling_admissible S r Ds hr hDs (snodes i) _ (childBudget _ _ (S.radius_pos r hr (snodes i)))
      have hexe : meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q =
          SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w main final sampling layers privateShift := by
        rw [meanCore,dite_eq_right hq]
      rw [hexe]
      constructor
      · exact SourceMeanQueryShift.queryShift M nodes anchors seeds S snodes r σ Ds δ t w main final
          smain sfinal layers hr hτ hm (fun i => (iq _ _ (M.radius_pos r hr (nodes i))).1)
          hpm hpf (fun i => (iq _ _ (S.radius_pos r hr (snodes i))).1)
          (fun i => (iq _ _ (S.radius_pos r hr (snodes i))).1)
      · have hm0 := SourceExecutableMass.build_mass_le M nodes anchors seeds r σ Ds main final sampling
          layers δ t w privateShift hr hpsi hm
        have hp0 := SamplingExecutableMass.private_weights_mass_le S snodes r Ds smain sfinal layers M hr hpm hpf
        have sums (count : ℕ) (children : Fin count → ExecutableData)
            (hb : ∀ i, shiftSq (children i).shiftVector ≤ C^(rank-1)) :
            (∑ i, shiftSq (children i).shiftVector) ≤ (count:ℝ)*C^(rank-1) := by
          calc
            _ ≤ ∑ _ : Fin count, C^(rank-1) := Finset.sum_le_sum (fun i _ => hb i)
            _ = _ := by simp
        have hsM := sums n main (fun i => childMass _ _ (M.radius_pos r hr (nodes i)))
        have hsp := sums ns smain (fun i => childMass _ _ (S.radius_pos r hr (snodes i)))
        have hsf := sums ns sfinal (fun i => childMass _ _ (S.radius_pos r hr (snodes i)))
        have hN : (0:ℝ) ≤ layers := by positivity
        have hX : 1 ≤ C^(rank-1) := one_le_pow₀ hC
        have hcm : C = 5+36*((layers:ℝ)*n+((layers:ℝ)+1)*ns) := by
          simp only [C,shiftBase,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
        have hcalc : 5+36*((layers:ℝ)*(∑ i,shiftSq (smain i).shiftVector)+
            ∑ i,shiftSq (sfinal i).shiftVector)+36*(layers:ℝ)*(∑ i,shiftSq (main i).shiftVector) ≤
            C*C^(rank-1) := by
          have hcmul := congrArg (fun z : ℝ => z*C^(rank-1)) hcm
          nlinarith [mul_le_mul_of_nonneg_left hsM hN,mul_le_mul_of_nonneg_left hsp hN]
        have hrec := hm0.trans (add_le_add hp0 le_rfl)
        have hpw : C*C^(rank-1) = C^rank := by
          rw [← pow_succ']
          congr 1
          omega
        exact hrec.trans (hcalc.trans hpw.le)

/-- Source-specialized mean: its private geometry is constructed internally,
so the private tau identity is discharged definitionally. -/
theorem mean_queryShift_and_mass
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (snodes : Fin ns ≃ mesh.Source m)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)
    (K scale : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
    (hbudget : shiftBase layers n ns ^ precisionRank (1/4) K ≤ Ds^2)
    (r σ q : ℝ) (hr : 0 < r) (hqK : q ≤ K) :
    let data := mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale r σ q
    QueryShift data.program data.enumeration data.coefficient r data.shiftVector ∧
      shiftSq data.shiftVector ≤ shiftBase layers n ns ^ precisionRank (1/4) q :=
  meanCore_queryShift_and_mass M nodes anchors seeds (privateGeometry M mesh) snodes
    Ds δ t w layers ht htq K scale hDs hpsi rfl hbudget r σ q hr hqK

end AcceleratedLogConcave.Oracle.RecursiveExecutable
