import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGadgetRecipe

/-! Exact fixed-scalar bookkeeping for literal positive-copy private gadgets.
The exponent counts actual unchanged source-row occurrences. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXScaleAux
open Holant Holant.Tractable
open scoped BigOperators
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget (Gadget denote)
end G
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type*} [CommSemiring K] {n m : ℕ}

theorem evaluate_scale (f : Signature K n) (c : K)
    (ps : List (Fin n→Bool ⊕ Fin m)) (x : Fin m→Bool) :
    B.evaluate (fun z=>c*f z) ps x=c^ps.length*B.evaluate f ps x := by
  induction ps with
  | nil => simp [B.evaluate]
  | cons p ps ih =>
    simp only [B.evaluate,List.map_cons,List.prod_cons,List.length_cons,pow_succ] at *
    rw [ih]
    ring

theorem gadget_scale (f : Signature K n) (c : K) (g : G.Gadget n m) :
    G.denote (fun z=>c*f z) g=fun z=>c^g.ports.length*G.denote f g z := by
  funext z
  unfold G.denote
  simp_rw [evaluate_scale]
  exact (Finset.mul_sum ..).symm

theorem nonaffine_scale {n : ℕ} (f : Signature AlgebraicComplex n)
    (bad : ¬Affine f) (c : AlgebraicComplex) (hc : c≠0) :
    ¬Affine (fun x=>c*f x) := by
  intro h
  have h' := h.scale c⁻¹
  apply bad
  convert h' using 1
  funext x
  simp [hc]

theorem nonproduct_scale {n : ℕ} (f : Signature AlgebraicComplex n)
    (bad : ¬Product f) (c : AlgebraicComplex) (hc : c≠0) :
    ¬Product (fun x=>c*f x) := by
  intro h
  have h' := h.scale c⁻¹
  apply bad
  convert h' using 1
  funext x
  simp [hc]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXScaleAux
end
