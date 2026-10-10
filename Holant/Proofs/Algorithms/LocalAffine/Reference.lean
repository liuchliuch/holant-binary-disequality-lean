import Holant.Proofs.Algorithms.LocalAffine.SupportSolver


namespace Holant.LocalDrafts.MainChain.LocalAffineReference
open Holant.Tractable AffinePhase
noncomputable section

variable (G : Network AlgebraicComplex 0)
variable (hv : ∀ v, LocalAffine (G.vertex v))
variable (he : ∀ e, LocalAffine (kernelSignature (G.edge e)))

def reference : Option ((Fin G.shape.edges × Bool) → Bool) :=
  (LocalAffineSupportSolver.solve (LocalAffineSupport.global G hv he)).map
    (LocalAffineSupport.assignment G.shape.edges)

theorem reference_supported (z : (Fin G.shape.edges × Bool) → Bool)
    (hz : reference G hv he = some z) : G.assignmentTerm Fin.elim0 z ≠ 0 := by
  cases h : LocalAffineSupportSolver.solve (LocalAffineSupport.global G hv he) with
  | none => simp [reference,h] at hz
  | some x =>
    have hzx : LocalAffineSupport.assignment G.shape.edges x = z := by
      simpa [reference,h] using hz
    have hx := LocalAffineSupportSolver.solve_sound _ x h
    have hn := (LocalAffineSupport.global_holds G hv he x).mp hx
    rwa [hzx] at hn

theorem reference_none_zero (hn : reference G hv he = none) : G.denote Fin.elim0 = 0 := by
  apply LocalAffineSupport.denote_zero_of_unsatisfiable G hv he
  apply (LocalAffineSupportSolver.solve_none_iff _).mp
  simpa [reference] using hn

theorem reference_some_affine (z : (Fin G.shape.edges × Bool) → Bool)
    (hz : reference G hv he = some z) :
    (LocalAffineNetwork.gauged G z).denote Fin.elim0 = G.denote Fin.elim0 ∧
      (∀ v, Affine ((LocalAffineNetwork.gauged G z).vertex v)) ∧
      ∀ e, Affine (kernelSignature ((LocalAffineNetwork.gauged G z).edge e)) := by
  have hn := reference_supported G hv he z hz
  exact ⟨LocalAffineNetwork.denote_gauged G z,
    LocalAffineNetwork.gauged_vertices_affine G hv z hn,
    LocalAffineNetwork.gauged_edges_affine G he z hn⟩

/-- Both branches use the result of the concrete solver, rather than a
classically selected satisfying assignment. Fixed local support tables remain
offline data. The zero answer need not mean that the equations had no solution. -/
theorem reference_correct :
    match reference G hv he with
    | none => G.denote Fin.elim0 = 0
    | some z =>
      (LocalAffineNetwork.gauged G z).denote Fin.elim0 = G.denote Fin.elim0 ∧
        (∀ v, Affine ((LocalAffineNetwork.gauged G z).vertex v)) ∧
        ∀ e, Affine (kernelSignature ((LocalAffineNetwork.gauged G z).edge e)) := by
  cases h : reference G hv he with
  | none => exact reference_none_zero G hv he h
  | some z => exact reference_some_affine G hv he z h

theorem reference_rounds :
    LocalAffineSupportSolver.rounds (LocalAffineSupport.global G hv he) ≤ 2*G.shape.edges :=
  LocalAffineSupportSolver.rounds_le _

end
end Holant.LocalDrafts.MainChain.LocalAffineReference
