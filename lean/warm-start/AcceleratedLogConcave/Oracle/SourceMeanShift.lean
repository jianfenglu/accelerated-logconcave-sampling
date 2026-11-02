import AcceleratedLogConcave.Oracle.SourceMeanExecutable
import AcceleratedLogConcave.Numerics.AffineBounds
import AcceleratedLogConcave.Oracle.ExecutableShiftTape

/-! Source algebra used by the actual nonterminal query-preserving shift.
The position-anchor coefficient and active-final invariance are derived from
the constructed graph, rather than assumed as a parent certificate. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceMeanShift
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open ExecutableShiftWeights SourceMeanExecutable
open scoped BigOperators

/-- Extracting the literal position coefficient agrees with the source ell_i. -/
theorem position_coefficient (M : MeanGeometry m) (r σ : ℝ) (i : M.MeanNode) :
    M.centerForm r σ i M.positionAtom = r * M.positionCoeff i := by
  have hv : M.direct r σ (0 : ℝ) 1 0 (fun _ _ => 0) i =
      M.centerForm r σ i M.positionAtom := by
    simp [MeanGeometry.direct, MeanGeometry.anchorValues, MeanGeometry.positionAtom,
      Fintype.sum_sum_type]
  exact hv.symm.trans (M.direct_positionCoeff r σ i)

theorem centerShift_eq (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (r σ : ℝ) (hr : 0 < r) (i : Fin n) :
    SourceMeanExecutable.centerShift M nodes r σ i =
      1 - M.positionCoeff (nodes i) / backwardEnd M.R := by
  unfold SourceMeanExecutable.centerShift
  rw [position_coefficient, mul_div_cancel_left₀ _ hr.ne']

/-- Active-final means have exactly ell=bStar, hence their centers stay fixed. -/
theorem centerShift_active (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (r σ : ℝ) (hr : 0 < r) (i : Fin m) :
    SourceMeanExecutable.centerShift M nodes r σ (nodes.symm (.center M i)) = 0 := by
  rw [centerShift_eq M nodes r σ hr, nodes.apply_symm_apply]
  simp only [MeanGeometry.positionCoeff, MeanGeometry.MeanNode.center,
    div_self M.backwardEnd_pos.ne', sub_self]

/-- The actual raw-shift center coefficient inherits the source ratio bound. -/
theorem centerShift_ratio (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (r σ : ℝ) (hr : 0 < r) (hpsi : M.psi ≤ M.R^4) (i : Fin n) :
    |SourceMeanExecutable.centerShift M nodes r σ i * r / M.radius r (nodes i)| ≤ 3 := by
  rw [centerShift_eq M nodes r σ hr]
  have h := M.shift_shape_le hpsi r hr (nodes i)
  rw [abs_div, abs_mul, abs_of_pos hr, abs_of_pos (M.radius_pos r hr (nodes i))]
  convert h using 1
  field_simp

/-- Varying the two source inputs translates the literal graph direct vector
by its extracted scalar coefficient, with every other anchor fixed. -/
theorem direct_translation (M : MeanGeometry m) (r σ : ℝ) (x Y G0 Δ : Point d)
    (ζ : Fin m → M.Kernel → Point d) (c : ℝ) (i : M.MeanNode) :
    M.direct r σ (x+Δ) (Y+c • Δ) G0 ζ i =
      M.direct r σ x Y G0 ζ i + (1 + M.centerForm r σ i M.positionAtom * c) • Δ := by
  simp only [MeanGeometry.direct, Fintype.sum_sum_type, MeanGeometry.anchorValues,
    Fintype.sum_unique, MeanGeometry.positionAtom, smul_add, smul_smul, add_smul, one_smul]
  abel

/-- The required private-anchor displacement produces the source k_i exactly. -/
theorem direct_parent_translation (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (r σ : ℝ) (hr : 0 < r) (x Y G0 Δ : Point d)
    (ζ : Fin m → M.Kernel → Point d) (i : Fin n) :
    M.direct r σ (x+Δ) (Y + (-1/(backwardEnd M.R*r)) • Δ) G0 ζ (nodes i) =
      M.direct r σ x Y G0 ζ (nodes i) + SourceMeanExecutable.centerShift M nodes r σ i • Δ := by
  rw [direct_translation]
  congr 2
  unfold SourceMeanExecutable.centerShift
  field_simp
  ring

/-- The reserve augmentation has exactly the required scaled-anchor effect. -/
theorem private_anchor_coefficient (M : MeanGeometry m) (r : ℝ) (hr : 0 < r) :
    backwardEnd M.R * (-1/r + ((M.R/backwardEnd M.R)/2)*((-2*M.R/backwardEnd M.R)/r)) =
      -1/(backwardEnd M.R*r) := by
  have hb := M.backwardEnd_pos.ne'
  have hsq : (backwardEnd M.R)^2 = 1-M.R^2 := by
    exact Real.sq_sqrt (by nlinarith [M.R_pos, M.R_le_half])
  field_simp [hb,hr.ne']
  nlinarith

/-- The direct rows really read the graph coefficients from their disjoint
region in the complete executable table. -/
theorem direct_table (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (sampling : ExecutableData) :
    SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling ∘
      (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.directSlot) =
      PrefixDirect.table M nodes anchors r σ := by
  funext j
  dsimp only [Function.comp_apply]
  erw [SourceMeanExecutable.table_prefix, PrefixPublicTable.table_direct]

/-- Local assembly only reads its source-prescribed retained-input split. -/
theorem assembly_table (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (sampling : ExecutableData) :
    SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling ∘
      (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.assemblySlot) =
      MeanGaussianSetup.table (SourceMeanExecutable.assembly M) := by
  funext j
  dsimp only [Function.comp_apply]
  erw [SourceMeanExecutable.table_prefix, PrefixPublicTable.table_assembly]

/-- The private call reads its own complete coefficient table, independently
of the main and final regions. -/
theorem private_table (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (sampling : ExecutableData) :
    SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling ∘
      (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.privateSlot) =
      sampling.coefficient := by
  funext j
  dsimp only [Function.comp_apply]
  erw [SourceMeanExecutable.table_prefix, PrefixPublicTable.table_private]

/-- Restoring a lowered child commutes with the literal structural translation. -/
theorem restore_translation (κ : Fin c → Fin C) (p : Program c .point)
    (x P : Ref Γ .point) (shift : GaussianSlot p → ℝ) (r : ℝ) (Δ : Point d)
    (tape : Tape d (p.embed κ x P)) :
    restoreTape κ p (fun s => nomatch s) x P
      (translate (p.embed κ x P)
        (lowerWeights κ p (fun s => nomatch s) x P shift) r Δ tape) =
      translate p shift r Δ (restoreTape κ p (fun s => nomatch s) x P tape) := by
  apply (lowerTapeEquiv κ p (fun s => nomatch s) x P).injective
  change lowerTape κ p (fun s => nomatch s) x P _ = lowerTape κ p (fun s => nomatch s) x P _
  erw [lowerTape_restoreTape, lowerTape_translate, lowerTape_restoreTape]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Full private-sampler execution transfers through its actual stored-input
embedding. The premise is a child execution lemma, discharged by the concrete
sampling program's translation theorem. -/
theorem embedded_translation (κ : Fin c → Fin C) (p : Program c .point)
    (x P : Ref Γ .point) (shift : GaussianSlot p → ℝ) (coeff : Fin c → ℝ)
    (r a : ℝ) (G : Point d → Point d) (input input' : Inputs d C)
    (env env' : Env d Γ) (Δ : Point d)
    (hcoeff : input'.coefficient = input.coefficient)
    (htable : input.coefficient ∘ κ = coeff)
    (hx : storedPoint env' x = storedPoint env x + Δ)
    (hP : storedPoint env' P = storedPoint env P)
    (hchild : ∀ (X Q : Point d) (tape : Tape d p),
      run p G ⟨coeff,X+Δ,Q⟩ Env.empty (translate p shift r Δ tape) =
        let result := run p G ⟨coeff,X,Q⟩ Env.empty tape
        (⟨(show Point d from result.value) + a • Δ,result.trace⟩ : Result d .point))
    (tape : Tape d (p.embed κ x P)) :
    run (p.embed κ x P) G input' env'
      (translate (p.embed κ x P) (lowerWeights κ p (fun s => nomatch s) x P shift) r Δ tape) =
      let result := run (p.embed κ x P) G input env tape
      (⟨(show Point d from result.value) + a • Δ,result.trace⟩ : Result d .point) := by
  rw [run_embed_every_tape, run_embed_every_tape]
  change (show Point d from env' x) = (show Point d from env x) + Δ at hx
  change (show Point d from env' P) = (show Point d from env P) at hP
  dsimp only at hx hP
  erw [restore_translation, hcoeff, htable, hx, hP]
  exact hchild (storedPoint env x) (storedPoint env P) _

section IncomingTape
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds : ℝ) (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (sampling : ExecutableData) (layers : ℕ) (privateShift : GaussianSlot sampling.program → ℝ)
    (Δ : Point d)
    (tape : Tape d (SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers))

/-- The local split coordinates are unchanged by the actual mean shift. -/
theorem incoming_raw (i : Fin (m+1)) :
    ((translate (SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers)
      (SourceMeanExecutable.incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift)
      r Δ tape).2.2.1 i).1 = (tape.2.2.1 i).1 := by
  change (show Point d from (tape.2.2.1 i).1) + (0/r) • Δ = _
  simp only [zero_div, zero_smul]
  exact add_zero _

/-- Conditional-flow Gaussian anchors are held fixed at every occurrence. -/
theorem incoming_flow (i : Fin h) :
    ((translate (SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers)
      (SourceMeanExecutable.incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift)
      r Δ tape).2.2.2.2.1 i).1 = (tape.2.2.2.2.1 i).1 := by
  change (show Point d from (tape.2.2.2.2.1 i).1) + (0/r) • Δ = _
  simp only [zero_div, zero_smul]
  exact add_zero _

/-- The exact continuation tape receives precisely the calculated mean-body weights. -/
theorem incoming_tail :
    (translate (SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers)
      (SourceMeanExecutable.incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift)
      r Δ tape).2.2.2.2.2.2 =
    translate (SourceMeanExecutable.body (a := a) (h := h) M nodes main final sampling layers)
      (SourceMeanExecutable.bodyShift M nodes r σ Ds main final sampling layers) r Δ tape.2.2.2.2.2.2 := rfl

/-- The paid private child receives its full separately augmented shift. -/
theorem incoming_private (i : Fin 1) :
    (translate (SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers)
      (SourceMeanExecutable.incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift)
      r Δ tape).1 i =
    translate (sampling.program.embed
      (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.privateSlot)
      (.there .here) .here)
      (lowerWeights (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.privateSlot)
        sampling.program (fun s => nomatch s) (.there .here) .here privateShift) r Δ (tape.1 i) := rfl
end IncomingTape

def inputEnv (x P : Point d) : Env d [.point,.point] :=
  Env.cons (d := d) (τ := .point) P (Env.cons (d := d) (τ := .point) x Env.empty)

section IncomingStore
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ) (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (sampling : ExecutableData)

/-- The retained-input split depends only on P and its own fresh Gaussian array. -/
def splitValues (P : Point d) (raw : Fin (m+1) → Point d) : Fin (m+1) → Point d :=
  MeanExecutablePrefix.assemblyValues
    (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.assemblySlot)
    ⟨SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling,0,P⟩ P raw

/-- The actual store delivered to the initialized main block. The unused raw
private return is retained below its scaled anchor, as in the executed syntax. -/
def cache (x P U : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d) :
    Env d (MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]) :=
  let Y := backwardEnd M.R • U
  let A := splitValues M nodes anchors r σ Ds δ t w main final sampling P raw
  let ζ := fun b ρ => Z (seeds.symm (b,ρ))
  let D := fun i => M.direct r σ x Y (A 0) ζ (nodes i)
  Env.prepend D (Env.prepend Z (Env.prepend A (Env.prepend raw
    (Env.prepend (fun _ : Fin 1 => Y) (Env.prepend (fun _ : Fin 1 => U)
      (inputEnv x P))))))

theorem cache_direct (x P U : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d) (i : Fin n) :
    storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z)
      (MeanExecutablePrefix.direct i) =
      M.direct r σ x (backwardEnd M.R • U)
        (splitValues M nodes anchors r σ Ds δ t w main final sampling P raw 0)
        (fun b ρ => Z (seeds.symm (b,ρ))) (nodes i) := by
  exact prepend_batchRef _ _ i

theorem cache_designated (x P U : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d)
    (i : Fin m) :
    storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z)
      (MeanExecutablePrefix.designated i) =
      splitValues M nodes anchors r σ Ds δ t w main final sampling P raw i.succ := by
  exact MeanExecutablePrefix.stored_designated _ _ _ _ _ _ _ i

theorem cache_retained (x P U : Point d) (raw : Fin (m+1) → Point d) (Z : Fin h → Point d) :
    storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling x P U raw Z)
      (MeanExecutablePrefix.saved (.here : Ref [.point,.point] .point)) = P := by
  dsimp only [cache]
  exact MeanExecutablePrefix.stored_saved _ _ _ _ _ _ _ .here

/-- The realized source cache has the exact source direct-center displacement;
its designated final inputs and retained P remain available separately. -/
theorem cache_direct_translation (hr : 0 < r) (x P U Δ : Point d)
    (raw : Fin (m+1) → Point d) (Z : Fin h → Point d) (i : Fin n) :
    let privateCoefficient := -1/r + ((M.R/backwardEnd M.R)/2)*((-2*M.R/backwardEnd M.R)/r)
    storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling
      (x+Δ) P (U + privateCoefficient • Δ) raw Z) (MeanExecutablePrefix.direct i) =
    storedPoint (cache M nodes anchors seeds r σ Ds δ t w main final sampling
      x P U raw Z) (MeanExecutablePrefix.direct i) + SourceMeanExecutable.centerShift M nodes r σ i • Δ := by
  dsimp only
  rw [cache_direct, cache_direct]
  rw [smul_add, smul_smul, private_anchor_coefficient M r hr]
  exact direct_parent_translation M nodes r σ hr x _ _ Δ _ i

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- Complete incoming execution, expressed in the literal source graph store. -/
theorem run_incoming (layers : ℕ) (G : Point d → Point d) (x P : Point d)
    (tape : Tape d (SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers)) :
    let input : Inputs d (SourceMeanExecutable.size (a := a) main final sampling) :=
      ⟨SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩
    let privateResult := run (sampling.program.embed
      (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.privateSlot)
      (.there .here) .here) G input (inputEnv x P) (tape.1 0)
    let tail := run (SourceMeanExecutable.body (a := a) (h := h) M nodes main final sampling layers)
      G input (cache M nodes anchors seeds r σ Ds δ t w main final sampling
        x P privateResult.value (fun i => (tape.2.2.1 i).1) (fun i => (tape.2.2.2.2.1 i).1))
      tape.2.2.2.2.2.2
    run (SourceMeanExecutable.incoming M nodes anchors seeds main final sampling layers) G input
      (inputEnv x P) tape =
      ⟨tail.value, privateResult.trace ++ List.ofFn (fun i : Fin (m+1) => Event.gaussian (SourceMeanExecutable.assemblyOrigin i)) ++
        List.ofFn (fun i : Fin h => Event.gaussian (SourceMeanExecutable.flowOrigin i)) ++ tail.trace⟩ := by
  dsimp only
  let input : Inputs d (SourceMeanExecutable.size (a := a) main final sampling) :=
    ⟨SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩
  have ht := MeanExecutablePrefix.run_code M anchors seeds sampling.size sampling.program
    (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.privateSlot)
    (SourceMeanExecutable.prefixSlot main final sampling PrefixPublicTable.scaleSlot) (.there .here) .here
    (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.assemblySlot)
    SourceMeanExecutable.assemblyOrigin SourceMeanExecutable.flowOrigin
    (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.directSlot)
    (SourceMeanExecutable.body (a := a) (h := h) M nodes main final sampling layers)
    G input (inputEnv x P) tape
  dsimp only at ht
  have hs : input.coefficient
      (SourceMeanExecutable.prefixSlot main final sampling PrefixPublicTable.scaleSlot) = backwardEnd M.R := by
    dsimp only [input]
    erw [SourceMeanExecutable.table_prefix, PrefixPublicTable.table_scale]
  have hd (Y G0 : Point d) (Z : Fin h → Point d) :
      MeanExecutablePrefix.directValues
        (SourceMeanExecutable.prefixSlot main final sampling ∘ PrefixPublicTable.directSlot) input x
        (MeanExecutablePrefix.anchorValues M anchors seeds Y G0 Z) =
      fun i => M.direct r σ x Y G0 (fun b ρ => Z (seeds.symm (b,ρ))) (nodes i) := by
    funext i
    exact MeanExecutablePrefix.directValues_eq_source M nodes anchors seeds r σ _ input
      (direct_table M nodes anchors r σ Ds δ t w main final sampling) x Y G0 Z i
  simp only [storedPoint, inputEnv, Env.cons_here, Env.cons_there] at ht
  simp only [hs, hd] at ht
  exact ht
end IncomingStore

/-- Convert a proved every-tape full execution identity to the canonical
Gaussian-slot formulation consumed by the child absorption compiler. -/
theorem queryShift_of_fullTranslation (data : ExecutableData) (r : ℝ)
    (h : ∀ (d : ℕ) (G : Point d → Point d) (x P Δ : Point d) (tape : Tape d data.program),
      run data.program G ⟨data.coefficient,x+Δ,P⟩ Env.empty
        (translate data.program data.shift r Δ tape) =
      run data.program G ⟨data.coefficient,x,P⟩ Env.empty tape) :
    ChildAbsorption.QueryShift data.program data.enumeration data.coefficient r data.shiftVector := by
  intro d G x P Δ z rest
  have ht := h d G x P Δ (joinTape data.program (fun s => z (data.enumeration s)) rest)
  rw [translate_joinTape] at ht
  simpa only [ExecutableData.shiftVector, Equiv.symm_apply_apply] using ht

end AcceleratedLogConcave.Oracle.SourceMeanShift
