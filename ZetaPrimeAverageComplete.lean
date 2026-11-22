module

public import Bernoulli.ZetaPrimeAverage
public import DedekindZetaZeroFree.Main
public import DedekindZetaZeroFree.LFunctions.Dedekind.ContinuationUniqueness
public import ZetaGrowthSetup

/-! The uniform prime-ideal estimate from the formal zero-free theorem. -/

namespace Bernoulli

/-- The canonical continuation is the continuation used by the upstream zero-free theorem. -/
public theorem dedekindZetaContinuationData (K : Type) [Field K] [NumberField K] :
    Nonempty (DedekindZetaContinuationData K) := by
  obtain ⟨ζ, Z, hζ, hZ, hright, hZE, hFE, hgrowth⟩ :=
    exists_dedekind_zeta_regularization_functional_equation K
  obtain ⟨f, hf, hfright, hfnz⟩ := DedekindZetaZeroFree.dedekindZeta_ne_zero K
  have hEq := DedekindZetaZeroFree.continuation_unique_off_one ζ f hζ hf
    (fun s hs => (hright s hs).trans (hfright s hs).symm)
  refine ⟨⟨ζ, Z, hZ, hZE, hright, ?_, ?_, hgrowth⟩⟩
  · intro s hs hne
    rw [show ζ s = f s from hEq hne]
    exact hfnz s hs hne
  · intro s hs
    simpa only [dedekindCompletionFactor, DedekindZetaZeroFree.AbelianQuotient.zetaGammaFactor]
      using hFE s hs

/-- The degree- and discriminant-uniform smoothed prime-ideal estimate. -/
public theorem uniformPrimeIdealEstimate : UniformPrimeIdealEstimate :=
  uniformPrimeIdealEstimate_of_continuation_data dedekindZetaContinuationData

end Bernoulli
