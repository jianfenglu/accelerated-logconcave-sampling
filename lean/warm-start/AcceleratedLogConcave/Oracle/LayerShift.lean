import AcceleratedLogConcave.Oracle.ChildAbsorption

/-! Actual auxiliary-tape translations for one synchronous Gaussian layer. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.LayerShift
open AcceleratedLogConcave.Oracle
open ChildAbsorption CovarianceSetup NoisyLayer TapeLowering AffineLowering Matrix
open scoped BigOperators

def rawShift (rho radius r k : ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun j => (k*r/radius) * (((childRoot rho radius v)⁻¹ *ᵥ v) j)

def shiftAux (w : Fin N → ℝ) (r : ℝ) (Δ : Point d)
    (z : Fin N → Point d) : Fin N → Point d :=
  fun j => z j + (w j/r) • Δ

def shiftFreshTape (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (κ : Fin (N*N+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (w : Fin N → ℝ) (r : ℝ) (Δ : Point d)
    (ω : Tape d (freshChild p e κ old designated auxiliary)) :
    Tape d (freshChild p e κ old designated auxiliary) :=
  let t := freshChildTapeEquiv p e κ old designated auxiliary
  let z := t ω
  t.symm (z.1,shiftAux w r Δ z.2.1,z.2.2)


theorem matrix_action_raw (h : Admissible rho radius Ds v) :
    childRoot rho radius v *ᵥ rawShift rho radius r k v =
      fun j => (k*r/radius)*v j := by
  change childRoot rho radius v *ᵥ ((k*r/radius) • ((childRoot rho radius v)⁻¹ *ᵥ v)) = _
  rw [mulVec_smul,mulVec_mulVec,(inverse_formula h).1,root_mul_explicitInverse h,one_mulVec]
  rfl

theorem transformShift {v : Fin N → ℝ} (h : Admissible rho radius Ds v) (hr : 0 < r)
    (Δ : Point d) (z : Fin N → Point d) (j : Fin N) :
    transformedGaussian (childRoot rho radius v) (shiftAux (rawShift rho radius r k v) r Δ z) j =
      transformedGaussian (childRoot rho radius v) z j + (v j/radius) • (k • Δ) := by
  have hv := congrFun (matrix_action_raw (r := r) (k := k) h) j
  have hc : (∑ t, childRoot rho radius v j t * (rawShift rho radius r k v t / r)) =
      (v j/radius)*k := by
    rw [show (∑ t, childRoot rho radius v j t * (rawShift rho radius r k v t / r)) =
      (∑ t, childRoot rho radius v j t * rawShift rho radius r k v t)/r by
        simp only [mul_div_assoc,Finset.sum_div]]
    change ((childRoot rho radius v *ᵥ rawShift rho radius r k v) j)/r = _
    rw [hv]
    field_simp
  simp only [transformedGaussian,shiftAux,smul_add,smul_smul,Finset.sum_add_distrib,
    ← Finset.sum_smul,hc]

theorem shiftBounds (h : Admissible rho radius Ds v) (hk : |k*r/radius| ≤ 3) :
    shiftSq (rawShift rho radius r k v) ≤ 36*shiftSq v ∧
    (∀ j, v j = 0 → rawShift rho radius r k v j = 0) ∧
    (k = 0 → rawShift rho radius r k v = 0) := by
  have hnorm := inverse_euclidean_bound h v
  have hb : (k*r/radius)^2 ≤ 9 := by
    have hab := abs_le.mp hk
    nlinarith
  have hmass : 0 ≤ shiftSq v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hi0 : 0 ≤ ∑ j, (((childRoot rho radius v)⁻¹ *ᵥ v) j)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : shiftSq (rawShift rho radius r k v) =
      (k*r/radius)^2 * ∑ j, (((childRoot rho radius v)⁻¹ *ᵥ v) j)^2 := by
    simp only [rawShift,shiftSq,mul_pow,Finset.mul_sum]
  constructor
  · rw [hn]
    have hm := mul_le_mul_of_nonneg_right hb hi0
    change (∑ j, (((childRoot rho radius v)⁻¹ *ᵥ v) j)^2) ≤ 4*shiftSq v at hnorm
    nlinarith
  constructor
  · intro j hj
    simp only [rawShift,inverse_action h,hj,zero_div,mul_zero]
  · intro hk0
    subst k
    funext j
    simp [rawShift]

theorem shiftAux_neg_cancel (w : Fin N → ℝ) (r : ℝ) (Δ : Point d) (z : Fin N → Point d) :
    shiftAux w r (-Δ) (shiftAux w r Δ z) = z := by
  funext j
  simp [shiftAux]

theorem freshTapeTranslation (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (κ : Fin (N*N+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (w : Fin N → ℝ) (r : ℝ) (Δ : Point d) :
    Function.Bijective (shiftFreshTape p e κ old designated auxiliary w r Δ) ∧
    ∀ ω, shiftFreshTape p e κ old designated auxiliary w r (-Δ)
      (shiftFreshTape p e κ old designated auxiliary w r Δ ω) = ω := by
  have hl : Function.LeftInverse (shiftFreshTape p e κ old designated auxiliary w r (-Δ))
      (shiftFreshTape p e κ old designated auxiliary w r Δ) := by
    intro ω
    simp only [shiftFreshTape,Equiv.apply_symm_apply,shiftAux_neg_cancel]
    exact Equiv.symm_apply_apply _ ω
  have hr : Function.RightInverse (shiftFreshTape p e κ old designated auxiliary w r (-Δ))
      (shiftFreshTape p e κ old designated auxiliary w r Δ) := by
    intro ω
    have hh := shiftAux_neg_cancel w r (-Δ)
    simp only [neg_neg] at hh
    simp only [shiftFreshTape,Equiv.apply_symm_apply,hh]
    exact Equiv.symm_apply_apply _ ω
  exact ⟨⟨hl.injective,hr.surjective⟩,hl⟩


theorem childExecutionTranslation (p : Program c .point) (e : GaussianSlot p ≃ Fin N)
    (κ : Fin (N*N+c) → Fin c') (old : Ref Γ .point)
    (designated : Origin) (auxiliary : Fin N → Origin)
    (rho radius Ds r k : ℝ) (v : Fin N → ℝ) (coeff : Fin c → ℝ)
    (h : Admissible rho radius Ds v) (hr : 0 < r) (hshift : QueryShift p e coeff radius v)
    (G : Point d → Point d) (input : Inputs d c') (env env' : Env d Γ) (Δ : Point d)
    (htable : input.coefficient ∘ κ = matrixTable (childRoot rho radius v) coeff)
    (hcenter : storedPoint env' old = storedPoint env old + k • Δ)
    (ω : Tape d (freshChild p e κ old designated auxiliary)) :
    run (freshChild p e κ old designated auxiliary) G input env'
      (shiftFreshTape p e κ old designated auxiliary (rawShift rho radius r k v) r Δ ω) =
    run (freshChild p e κ old designated auxiliary) G input env ω := by
  let data := freshChildTapeEquiv p e κ old designated auxiliary ω
  have hz : (fun s => transformedGaussian (childRoot rho radius v)
      (shiftAux (rawShift rho radius r k v) r Δ data.2.1) (e s)) =
      (fun s => transformedGaussian (childRoot rho radius v) data.2.1 (e s) +
        (v (e s)/radius) • (k • Δ)) := by
    funext s
    exact transformShift h hr Δ data.2.1 (e s)
  have hs := hshift d G (storedPoint env old) data.1 (k • Δ)
    (transformedGaussian (childRoot rho radius v) data.2.1) data.2.2
  have ht := run_freshChild p e κ old designated auxiliary (childRoot rho radius v)
    coeff G input env' htable
      (shiftFreshTape p e κ old designated auxiliary (rawShift rho radius r k v) r Δ ω)
  have hb := run_freshChild p e κ old designated auxiliary (childRoot rho radius v)
    coeff G input env htable ω
  simp only [shiftFreshTape,Equiv.apply_symm_apply] at ht
  change run (freshChild p e κ old designated auxiliary) G input env'
      (shiftFreshTape p e κ old designated auxiliary (rawShift rho radius r k v) r Δ ω) =
    ⟨(run p G ⟨coeff,storedPoint env' old,data.1⟩ Env.empty
       (transformedSourceTape p e (childRoot rho radius v)
         (shiftAux (rawShift rho radius r k v) r Δ data.2.1) data.2.2)).value,
     [Event.gaussian designated] ++ List.ofFn (fun j => Event.gaussian (auxiliary j)) ++
       (run p G ⟨coeff,storedPoint env' old,data.1⟩ Env.empty
       (transformedSourceTape p e (childRoot rho radius v)
         (shiftAux (rawShift rho radius r k v) r Δ data.2.1) data.2.2)).trace.filter keepNonGaussian⟩ at ht
  rw [hcenter] at ht
  simp only [transformedSourceTape] at ht hb
  rw [hz,hs] at ht
  exact ht.trans hb.symm

/-- Translate only the literal auxiliary slots of every executed child. -/
def shiftLayerData (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ) (r : ℝ) (Δ : Point d)
    (data : LayerData c p next d) : LayerData c p next d :=
  ⟨(fun i => ((data.1 i).1,shiftAux (w i) r Δ (data.1 i).2.1,(data.1 i).2.2)),
    data.2.1,data.2.2⟩

def shiftLayerTape (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ) (r : ℝ) (Δ : Point d)
    (ω : Tape d (noisyLayer c p e old direct outer designated residual auxiliary next)) :
    Tape d (noisyLayer c p e old direct outer designated residual auxiliary next) :=
  let t := layerTapeEquiv c p e old direct outer designated residual auxiliary next
  t.symm (shiftLayerData c p next w r Δ (t ω))


/-- A closed actual layer returns one computed row. It executes and charges all
children and all residual draws, even when the selected output ignores them. -/
def layerOutput (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin) (j : Fin n) :=
  noisyLayer c p e old direct outer designated residual auxiliary (.ret (batchRef j))



theorem shiftLayerData_neg_cancel (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ) (r : ℝ) (Δ : Point d)
    (data : LayerData c p next d) :
    shiftLayerData c p next w r (-Δ) (shiftLayerData c p next w r Δ data) = data := by
  simp only [shiftLayerData,shiftAux_neg_cancel]

theorem layerTapeTranslation (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (next : Prog (publicSize c p) (nextCtx n Γ) τ)
    (w : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ) (r : ℝ) (Δ : Point d) :
    Function.Bijective (shiftLayerTape c p e old direct outer designated residual auxiliary next w r Δ) ∧
    ∀ ω, shiftLayerTape c p e old direct outer designated residual auxiliary next w r (-Δ)
      (shiftLayerTape c p e old direct outer designated residual auxiliary next w r Δ ω) = ω := by
  have hl : Function.LeftInverse
      (shiftLayerTape c p e old direct outer designated residual auxiliary next w r (-Δ))
      (shiftLayerTape c p e old direct outer designated residual auxiliary next w r Δ) := by
    intro ω
    simp only [shiftLayerTape,Equiv.apply_symm_apply,shiftLayerData_neg_cancel]
    exact Equiv.symm_apply_apply _ ω
  have hr : Function.RightInverse
      (shiftLayerTape c p e old direct outer designated residual auxiliary next w r (-Δ))
      (shiftLayerTape c p e old direct outer designated residual auxiliary next w r Δ) := by
    intro ω
    have hh := shiftLayerData_neg_cancel c p next w r (-Δ)
    simp only [neg_neg] at hh
    simp only [shiftLayerTape,Equiv.apply_symm_apply,hh]
    exact Equiv.symm_apply_apply _ ω
  exact ⟨⟨hl.injective,hr.surjective⟩,hl⟩

theorem totalShiftBound (N : Fin n → ℕ) (rho r : ℝ) (radius Ds k : Fin n → ℝ)
    (v : ∀ i, Fin (N i) → ℝ)
    (h : ∀ i, Admissible rho (radius i) (Ds i) (v i))
    (hk : ∀ i, |k i*r/radius i| ≤ 3) :
    (∑ i, shiftSq (rawShift rho (radius i) r (k i) (v i))) ≤ 36 * ∑ i, shiftSq (v i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (shiftBounds (h i) (hk i)).1)

theorem run_layerOutput (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (j : Fin n) (G : Point d → Point d) (input : Inputs d (publicSize c p)) (env : Env d Γ)
    (ω : Tape d (layerOutput c p e old direct outer designated residual auxiliary j)) :
    let children := fun i => run (freshChild (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i)) G input env (ω.1 i)
    let Q := fun i => (children i).value
    let Z := fun i => (ω.2.1 i).1
    run (layerOutput c p e old direct outer designated residual auxiliary j) G input env ω =
      ⟨noisyValues (aSlot c p) (residualSlot c p) direct input env Q Z j,
       ((List.ofFn (fun i => (children i).trace)).flatten ++
         List.ofFn (fun i => Event.gaussian (residual i))).map (Event.withPrefix outer)⟩ := by
  have ht := run_noisyLayer c p e old direct outer designated residual auxiliary
    (.ret (batchRef j)) G input env ω
  have hv (xs : Fin n → Point d) (ρ : Env d (noiseCtx n Γ)) :
      Env.prepend xs ρ (batchRef j) = xs j := prepend_batchRef xs ρ j
  simpa only [layerOutput,run,hv,List.append_nil] using ht


theorem layerExecutionTranslation (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (rho r : ℝ) (radius Ds k : Fin n → ℝ)
    (v : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → ℝ) (coeff : ∀ i, Fin (c i) → ℝ)
    (h : ∀ i, Admissible rho (radius i) (Ds i) (v i)) (hr : 0 < r)
    (hshift : ∀ i, QueryShift (p i) (e i) (coeff i) (radius i) (v i))
    (A C : Fin n → Fin n → ℝ) (hostX hostP : Point d) (G : Point d → Point d)
    (env env' : Env d Γ) (Δ : Point d)
    (hold : ∀ i, storedPoint env' (old i) = storedPoint env (old i) + k i • Δ)
    (hdir : ∀ i, storedPoint env' (direct i) = storedPoint env (direct i) + k i • Δ)
    (j : Fin n) (ω : Tape d (layerOutput c p e old direct outer designated residual auxiliary j)) :
    let input : Inputs d (publicSize c p) :=
      ⟨layerTable c p A C (fun i => childRoot rho (radius i) (v i)) coeff,hostX,hostP⟩
    let shifted := shiftLayerTape c p e old direct outer designated residual auxiliary
      (.ret (batchRef j)) (fun i => rawShift rho (radius i) r (k i) (v i)) r Δ ω
    let result := run (layerOutput c p e old direct outer designated residual auxiliary j) G input env ω
    run (layerOutput c p e old direct outer designated residual auxiliary j) G input env' shifted =
      ⟨(show Point d from result.value) + k j • Δ,result.trace⟩ := by
  let input : Inputs d (publicSize c p) :=
    ⟨layerTable c p A C (fun i => childRoot rho (radius i) (v i)) coeff,hostX,hostP⟩
  let shifted := shiftLayerTape c p e old direct outer designated residual auxiliary
    (.ret (batchRef j)) (fun i => rawShift rho (radius i) r (k i) (v i)) r Δ ω
  have hc (i : Fin n) :
      run (freshChild (p i) (e i) (childSlot c p i) (old i) (designated i) (auxiliary i))
        G input env' (shifted.1 i) =
      run (freshChild (p i) (e i) (childSlot c p i) (old i) (designated i) (auxiliary i))
        G input env (ω.1 i) := by
    change run (freshChild (p i) (e i) (childSlot c p i) (old i) (designated i) (auxiliary i))
      G input env' (shiftFreshTape (p i) (e i) (childSlot c p i) (old i)
        (designated i) (auxiliary i) (rawShift rho (radius i) r (k i) (v i)) r Δ (ω.1 i)) = _
    exact childExecutionTranslation (p i) (e i) (childSlot c p i) (old i)
      (designated i) (auxiliary i) rho (radius i) (Ds i) r (k i) (v i) (coeff i)
      (h i) hr (hshift i) G input env env' Δ
      (funext (fun t => layerTable_child c p A C (fun a => childRoot rho (radius a) (v a)) coeff i t)) (hold i) (ω.1 i)
  have ha := run_layerOutput c p e old direct outer designated residual auxiliary j G input env' shifted
  have hb := run_layerOutput c p e old direct outer designated residual auxiliary j G input env ω
  dsimp only at ha hb
  simp only [hc] at ha
  change run (layerOutput c p e old direct outer designated residual auxiliary j) G input env' shifted =
    ⟨(show Point d from (run (layerOutput c p e old direct outer designated residual auxiliary j)
      G input env ω).value) + k j • Δ,
      (run (layerOutput c p e old direct outer designated residual auxiliary j) G input env ω).trace⟩
  rw [ha,hb]
  congr 1
  change noisyValues (aSlot c p) (residualSlot c p) direct input env' _ _ j =
    noisyValues (aSlot c p) (residualSlot c p) direct input env _ _ j + k j • Δ
  simp only [noisyValues,hdir]
  abel

theorem executedCount_layerOutput (kind : EventKind)
    (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
    (e : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
    (old direct : Fin n → Ref Γ .point) (outer : Origin)
    (designated residual : Fin n → Origin)
    (auxiliary : ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
    (j : Fin n) (G : Point d → Point d) (input : Inputs d (publicSize c p)) (env : Env d Γ)
    (ω : Tape d (layerOutput c p e old direct outer designated residual auxiliary j)) :
    shapeCount kind ((run (layerOutput c p e old direct outer designated residual auxiliary j)
      G input env ω).trace.map Event.erase) =
      if kind = .gaussian then n + (∑ i, (tapeShape (p i)).gaussianBlocks) + n
        else ∑ i, syntaxCount kind (p i) := by
  simpa only [layerOutput,syntaxCount,Nat.add_zero] using
    (executedCount_noisyLayer c p e old direct outer designated residual auxiliary
      (.ret (batchRef j)) kind G input env ω)

end AcceleratedLogConcave.Oracle.LayerShift


