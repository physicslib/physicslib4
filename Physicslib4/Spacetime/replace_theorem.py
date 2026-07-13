import os
os.chdir("/data/clones/physicslib/physicslib4/aqft-in-lean")

with open("Physicslib4/Spacetime/scratch_flatConnectionMinkowskiCarrier_metricCompatible.lean", "r") as f:
    content = f.read()

old_start = "/-- `flatConnectionMinkowskiCarrier` is compatible with the constant Minkowski"
old_end = "simpa [flatConnectionMinkowskiCarrier, hI_J]"

start_idx = content.find(old_start)
end_idx = content.find(old_end, start_idx)
if start_idx == -1 or end_idx == -1:
    print("Could not find the theorem block", flush=True)
    exit(1)

end_of_line = content.find("\n", end_idx)
if end_of_line == -1:
    end_of_line = len(content)

new_theorem = """/-- `flatConnectionMinkowskiCarrier` is compatible with the constant Minkowski
metric, hence is the Levi-Civita connection. -/
theorem flatConnectionMinkowskiCarrier_metricCompatible :
    Spacetime.IsMetricCompatible (Carrier := MinkowskiSpacetimeCarrier)
      (fun _ => minkowskiForm) flatConnectionMinkowskiCarrier := by
  intro σ τ x X₀ hσ hτ
  let I_model : ModelWithCorners ℝ SpacetimeModel SpacetimeModel :=
    modelWithCornersSelf ℝ SpacetimeModel
  let J_model : ModelWithCorners ℝ SpacetimeModel SpacetimeModel :=
    𝓘(ℝ, SpacetimeModel)
  have hI_J : I_model = J_model := rfl
  -- Write the LHS as mfderiv I_model 𝓘(ℝ) (B ∘ h) x X₀ where
  --   h(y) = (σ y, τ y) : M → SpacetimeModel × SpacetimeModel
  --   B(p,q) = minkowskiForm p q : SpacetimeModel × SpacetimeModel → ℝ
  set h : MinkowskiSpacetimeCarrier → SpacetimeModel × SpacetimeModel :=
    fun y => (σ y, τ y) with hh
  set B : SpacetimeModel × SpacetimeModel → ℝ :=
    fun (p, q) => minkowskiForm p q with hB
  -- h is MDifferentiableAt because σ and τ are
  have hh_mdiff : MDifferentiableAt I_model (I_model.prod I_model) h x :=
    MDifferentiableAt.prodMk hσ hτ
  -- B is differentiable at (h x) because it is a continuous bilinear map
  have hB_diff : DifferentiableAt ℝ B (h x) :=
    (minkowskiForm.hasFDerivAt_of_bilinear (hf := hasFDerivAt_fst (p := h x))
      (hg := hasFDerivAt_snd (p := h x))).differentiableAt
  have hB_mdiff : MDifferentiableAt (I_model.prod I_model) 𝓘(ℝ) B (h x) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hB_diff
  -- Chain rule
  have hchain : mfderiv I_model 𝓘(ℝ) (B ∘ h) x =
      (mfderiv (I_model.prod I_model) 𝓘(ℝ) B (h x)).comp (mfderiv I_model (I_model.prod I_model) h x) := by
    apply mfderiv_comp hB_mdiff hh_mdiff
  -- mfderiv of B = fderiv of B (since domain is a normed space)
  have hmfderiv_B : mfderiv (I_model.prod I_model) 𝓘(ℝ) B (h x) = fderiv ℝ B (h x) := by
    rw [mfderiv_eq_fderiv]
  -- mfderiv of h = product of mfderiv of σ and τ
  have hmfderiv_h : mfderiv I_model (I_model.prod I_model) h x =
      (mfderiv I_model J_model σ x).prod (mfderiv I_model J_model τ x) :=
    mfderiv_prodMk hσ hτ
  -- fderiv of B at (h x) = (σ x, τ x) computed via fderiv_of_bilinear
  have hfderiv_B : fderiv ℝ B (h x) =
      minkowskiForm.precompR (SpacetimeModel × SpacetimeModel) (σ x) (fderiv ℝ Prod.snd (h x))
      + minkowskiForm.precompL (SpacetimeModel × SpacetimeModel) (fderiv ℝ Prod.fst (h x)) (τ x) :=
    minkowskiForm.fderiv_of_bilinear
      (hf := (hasFDerivAt_fst (p := h x)).differentiableAt)
      (hg := (hasFDerivAt_snd (p := h x)).differentiableAt)
  have h_aux : mvfderiv I_model (fun y => minkowskiForm (σ y) (τ y)) x X₀ =
      minkowskiForm (σ x) (mvfderiv I_model τ x X₀) + minkowskiForm (mvfderiv I_model σ x X₀) (τ x) := by
    calc
      mvfderiv I_model (fun y => minkowskiForm (σ y) (τ y)) x X₀
          = mfderiv I_model 𝓘(ℝ) (fun y => minkowskiForm (σ y) (τ y)) x X₀ := rfl
      _ = mfderiv I_model 𝓘(ℝ) (B ∘ h) x X₀ := by
        simp [hB, hh]
      _ = ((mfderiv (I_model.prod I_model) 𝓘(ℝ) B (h x)).comp (mfderiv I_model (I_model.prod I_model) h x)) X₀ := by
        rw [hchain]
      _ = (fderiv ℝ B (h x)) ((mfderiv I_model (I_model.prod I_model) h x) X₀) := by
        rw [hmfderiv_B, ContinuousLinearMap.comp_apply]
      _ = (fderiv ℝ B (h x)) (((mfderiv I_model J_model σ x).prod (mfderiv I_model J_model τ x)) X₀) := by
        rw [hmfderiv_h]
      _ = (fderiv ℝ B (h x)) (mfderiv I_model J_model σ x X₀, mfderiv I_model J_model τ x X₀) := rfl
      _ = (minkowskiForm.precompR (SpacetimeModel × SpacetimeModel) (σ x) (fderiv ℝ Prod.snd (h x))
            + minkowskiForm.precompL (SpacetimeModel × SpacetimeModel) (fderiv ℝ Prod.fst (h x)) (τ x))
          (mfderiv I_model J_model σ x X₀, mfderiv I_model J_model τ x X₀) := by
        rw [hfderiv_B]
      _ = minkowskiForm (σ x) (fderiv ℝ Prod.snd (h x) (mfderiv I_model J_model σ x X₀, mfderiv I_model J_model τ x X₀))
          + minkowskiForm (fderiv ℝ Prod.fst (h x) (mfderiv I_model J_model σ x X₀, mfderiv I_model J_model τ x X₀)) (τ x) := by
        simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply]
      _ = minkowskiForm (σ x) (mfderiv I_model J_model τ x X₀)
          + minkowskiForm (mfderiv I_model J_model σ x X₀) (τ x) := by
        simp [ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply,
          ContinuousLinearMap.fderiv, fderiv_fst, fderiv_snd]
      _ = minkowskiForm (σ x) (mvfderiv I_model τ x X₀)
          + minkowskiForm (mvfderiv I_model σ x X₀) (τ x) := by
        simp [mvfderiv, hI_J]
  -- Now rewrite the RHS of the goal using flatConnectionMinkowskiCarrier = mvfderiv I_model
  simpa [flatConnectionMinkowskiCarrier, hI_J]"""

content = content[:start_idx] + new_theorem + content[end_of_line+1:]

with open("Physicslib4/Spacetime/scratch_flatConnectionMinkowskiCarrier_metricCompatible.lean", "w") as f:
    f.write(content)

print("Done", flush=True)