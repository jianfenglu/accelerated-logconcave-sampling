import AcceleratedLogConcave.Analysis.BackwardComparison

/-! Forward comparison on an arbitrary closed interval.
This is a scalar comparison lemma, not a reversal or renaming of a backward
flow theorem. No division by the interval length or curvature occurs. -/
noncomputable section
open Set Filter
open scoped Topology
namespace AcceleratedLogConcave.Analysis.FixedCut
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Translate the initial endpoint to zero and retain closed-slab derivatives. -/
theorem forward_closed_comparison {X X' : ℝ → V} {a f B : ℝ → ℝ} {ρ b K : ℝ}
    (hX : ContinuousOn X (Icc ρ b))
    (hX' : ∀ s ∈ Icc ρ b, HasDerivWithinAt X (X' s) (Icc ρ b) s)
    (hB : ContinuousOn B (Icc ρ b))
    (hB' : ∀ s ∈ Icc ρ b, HasDerivWithinAt B (a s * B s + f s) (Icc ρ b) s)
    (hρ : ‖X ρ‖ ≤ B ρ)
    (ha : ∀ s ∈ Icc ρ b, a s ≤ K)
    (hbound : ∀ s ∈ Icc ρ b, ‖X' s‖ ≤ a s * ‖X s‖ + f s)
    {t : ℝ} (ht : t ∈ Icc ρ b) : ‖X t‖ ≤ B t := by
  have hm (s : ℝ) (hs : s ∈ Icc 0 (b-ρ)) : ρ+s ∈ Icc ρ b := by
    constructor <;> linarith [hs.1,hs.2]
  have hh (s : ℝ) : HasDerivAt (fun u : ℝ => ρ+u) 1 s := by
    simpa using (hasDerivAt_id s).const_add ρ
  have hZ (s : ℝ) (hs : s ∈ Ico 0 (b-ρ)) :
      HasDerivWithinAt (fun u => X (ρ+u)) (X' (ρ+s)) (Ici s) s := by
    have hd := (hX' (ρ+s) (hm s ⟨hs.1,hs.2.le⟩)).hasFDerivWithinAt.comp_hasDerivWithinAt
      s (hh s).hasDerivWithinAt hm
    have hd' : HasDerivWithinAt (fun u => X (ρ+u)) (X' (ρ+s)) (Icc 0 (b-ρ)) s := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, Function.comp_def] using hd
    apply hd'.mono_of_mem_nhdsWithin
    exact inter_mem
      (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hs.1))
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hs.2))
  have hR (s : ℝ) (hs : s ∈ Ico 0 (b-ρ)) :
      HasDerivWithinAt (fun u => B (ρ+u))
        (a (ρ+s)*B (ρ+s)+f (ρ+s)) (Ici s) s := by
    have hd := (hB' (ρ+s) (hm s ⟨hs.1,hs.2.le⟩)).hasFDerivWithinAt.comp_hasDerivWithinAt
      s (hh s).hasDerivWithinAt hm
    have hd' : HasDerivWithinAt (fun u => B (ρ+u))
        (a (ρ+s)*B (ρ+s)+f (ρ+s)) (Icc 0 (b-ρ)) s := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, Function.comp_def] using hd
    apply hd'.mono_of_mem_nhdsWithin
    exact inter_mem
      (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hs.1))
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hs.2))
  have h := forward_comparison
    (hX.comp (continuous_const.add continuous_id).continuousOn hm) hZ
    (hB.comp (continuous_const.add continuous_id).continuousOn hm) hR
    (by simpa using hρ)
    (fun s hs => ha (ρ+s) (hm s ⟨hs.1,hs.2.le⟩))
    (fun s hs => hbound (ρ+s) (hm s ⟨hs.1,hs.2.le⟩))
    (show t-ρ ∈ Icc 0 (b-ρ) by constructor <;> linarith [ht.1,ht.2])
  have hshift : ρ+(t-ρ) = t := by ring
  simpa only [Function.comp_def, Pi.add_apply, id_eq, hshift] using h

/-- The actual forward quadratic clock, not the backward clock. -/
theorem forward_homogeneous_bound {X X' : ℝ → V} {α ρ b δ : ℝ}
    (hα : 0 ≤ α)
    (hX : ContinuousOn X (Icc ρ b))
    (hX' : ∀ s ∈ Icc ρ b, HasDerivWithinAt X (X' s) (Icc ρ b) s)
    (hρ : ‖X ρ‖ ≤ δ)
    (hbound : ∀ s ∈ Icc ρ b, ‖X' s‖ ≤ α*s*‖X s‖)
    {t : ℝ} (ht : t ∈ Icc ρ b) :
    ‖X t‖ ≤ δ * Real.exp (α*(t^2-ρ^2)/2) := by
  let B : ℝ → ℝ := fun s => δ * Real.exp (α*(s^2-ρ^2)/2)
  have hd (s : ℝ) : HasDerivAt B (α*s*B s) s := by
    have hp : HasDerivAt (fun u : ℝ => α*(u^2-ρ^2)/2) (α*s) s := by
      convert ((((hasDerivAt_id s).pow 2).sub_const (ρ^2)).const_mul α).div_const 2 using 1
      · rfl
      · dsimp; ring
    convert hp.exp.const_mul δ using 1
    dsimp [B]; ring
  apply forward_closed_comparison (f := fun _ => 0) hX hX'
    (fun s _ => (hd s).continuousAt.continuousWithinAt)
    (fun s _ => by simpa using (hd s).hasDerivWithinAt)
    (by simpa [B] using hρ)
    (K := α*b) (fun s hs => mul_le_mul_of_nonneg_left hs.2 hα)
    (fun s hs => by simpa using hbound s hs) ht

/-- A proportional forcing estimate with zero initial data. -/
theorem forward_proportional_forcing {X X' : ℝ → V} {α ρ b C : ℝ}
    (hα : 0 ≤ α)
    (hX : ContinuousOn X (Icc ρ b))
    (hX' : ∀ s ∈ Icc ρ b, HasDerivWithinAt X (X' s) (Icc ρ b) s)
    (hρ : X ρ = 0)
    (hbound : ∀ s ∈ Icc ρ b, ‖X' s‖ ≤ α*s*‖X s‖ + α*s*C)
    {t : ℝ} (ht : t ∈ Icc ρ b) :
    ‖X t‖ ≤ C * (Real.exp (α*(t^2-ρ^2)/2)-1) := by
  let B : ℝ → ℝ := fun s => C * (Real.exp (α*(s^2-ρ^2)/2)-1)
  have hd (s : ℝ) : HasDerivAt B (α*s*B s+α*s*C) s := by
    have hp : HasDerivAt (fun u : ℝ => α*(u^2-ρ^2)/2) (α*s) s := by
      convert ((((hasDerivAt_id s).pow 2).sub_const (ρ^2)).const_mul α).div_const 2 using 1
      · rfl
      · dsimp; ring
    convert (hp.exp.sub_const 1).const_mul C using 1
    dsimp [B]; ring
  exact forward_closed_comparison hX hX'
    (fun s _ => (hd s).continuousAt.continuousWithinAt)
    (fun s _ => (hd s).hasDerivWithinAt)
    (by simp [B,hρ])
    (K := α*b) (fun s hs => mul_le_mul_of_nonneg_left hs.2 hα) hbound ht
end AcceleratedLogConcave.Analysis.FixedCut
